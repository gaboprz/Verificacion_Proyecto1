//================================================================================
// Clase para reportar resultados al Scoreboard
//================================================================================
class checker_result;
    // Información de la verificación
    bit         test_passed;
    string      test_description;
    string      error_message;
    realtime    timestamp;

    // identificadores de secuencia
    int         rx_seq_id;
    int         tx_seq_id;

    // Datos relevantes
    logic [31:0] rx_data;
    logic [1:0]  rx_offset;
    logic [2:0]  rx_size;
    logic [31:0] tx_data;
    logic [1:0]  tx_offset;
    logic [2:0]  tx_size;
    logic [2:0]  config_size;
    logic [1:0]  config_offset;

    // Trazabilidad y golden
    string       rx_contributors;     // “(RX#2 ... bytes=[2:0xAA]) (RX#3 ... )”
    logic [31:0] golden_expected;

    // Contadores internos (si quieres usarlos luego)
    int checks_passed;
    int checks_failed;

    function void print(string tag="");
        $display("T=%0t %s ============================================", $time, tag);
        $display("T=%0t %s TEST: %s", $time, tag, test_description);
        $display("T=%0t %s RESULT: %s", $time, tag, test_passed ? "PASSED" : "FAILED");
        $display("T=%0t %s INFO: %s", $time, tag, error_message);
        $display("T=%0t %s SEQ: RX=%0d  TX=%0d", $time, tag, rx_seq_id, tx_seq_id);
        $display("T=%0t %s Config: SIZE=%0d, OFFSET=%0d", $time, tag, config_size, config_offset);

        // RX
        $display("T=%0t %s RX: data=0x%08h, offset=%0d, size=%0d",
                 $time, tag, rx_data, rx_offset, rx_size);

        // TX + detalle
        if (tx_seq_id == 0 && tx_size == 0)
            $display("T=%0t %s TX: N/A (aún no emparejado)", $time, tag);
        else begin
            $display("T=%0t %s TX: data=0x%08h, offset=%0d, size=%0d",
                     $time, tag, tx_data, tx_offset, tx_size);
            $display("T=%0t %s RX contributors: %s", $time, tag, rx_contributors);
            $display("T=%0t %s Golden expected: 0x%08h", $time, tag, golden_expected);
        end

        $display("T=%0t %s ============================================", $time, tag);
    endfunction
endclass

// Definir mailbox específico para checker_result
typedef mailbox #(checker_result) checker_result_mbx;

//================================================================================
// Clase principal del Checker
//================================================================================
class aligner_checker;

    //==============================
    // MAILBOXES
    //==============================
    trans_apb_in_mbx    apb_config_mbx;   // Config APB desde generador
    trans_rx_in_mbx     rx_in_mbx;        // RX del generador
    trans_rx_out_mbx    rx_out_mbx;       // Respuesta RX del monitor
    trans_tx_out_mbx    tx_out_mbx;       // TX del monitor
    checker_result_mbx  chk_scb_mbx;      // Hacia scoreboard

    //==============================
    // ESTADO DE CONFIG
    //==============================
    localparam int ALGN_DATA_WIDTH = 32;
    localparam int DATA_BYTES      = ALGN_DATA_WIDTH/8; // 4
    logic [2:0] current_size   = 1; // reset
    logic [1:0] current_offset = 0; // reset

    bit legal;

    //==============================
    // COLAS / TRACES
    //==============================
    typedef struct {
        int           rx_seq;          // secuencia RX de donde salió el byte
        byte unsigned value;           // el byte en sí
        logic [31:0]  rx_data;         // palabra RX origen (para imprimir)
        byte unsigned idx_in_rx;       // índice del byte dentro de esa palabra (0..3)
        logic [1:0]   rx_offset;       // offset del RX origen
        logic [2:0]   rx_size;         // size del RX origen
    } byte_entry_t;

    byte_entry_t golden_fifo[$];       // bytes en orden de llegada con trazabilidad

    typedef struct {
        int         seq;
        trans_rx_in rx;
    } rx_item_t;

    rx_item_t rx_for_tx_q[$];          // RX legales pendientes

    // Contadores
    int total_checks = 0;
    int passed_checks = 0;
    int failed_checks = 0;
    int illegal_transfers_detected = 0;
    int alignment_checks = 0;

    // Secuencia de RX / TX
    int rx_seq_counter = 0;
    int tx_seq_counter = 0;

    //==============================
    // UTILIDADES
    //==============================
    function automatic bit validate_rx_transfer(logic [1:0] offset, logic [2:0] size);
        if (!(size inside {1,2,4})) return 0;
        return (((DATA_BYTES + offset) % size) == 0);
    endfunction

    function automatic void push_rx_bytes_to_golden(trans_rx_in rx, int rx_seq_id);
        byte unsigned bytes[DATA_BYTES];
        byte_entry_t be;
        int i;
        int idx;

        // desglosar bytes de la palabra RX
        bytes[0] = rx.md_rx_data[7:0];
        bytes[1] = rx.md_rx_data[15:8];
        bytes[2] = rx.md_rx_data[23:16];
        bytes[3] = rx.md_rx_data[31:24];

        for (i = 0; i < rx.md_rx_size; i++) begin
            idx = rx.md_rx_offset + i;
            if (idx < DATA_BYTES) begin
                be.rx_seq    = rx_seq_id;
                be.value     = bytes[idx];
                be.rx_data   = rx.md_rx_data;
                be.idx_in_rx = idx;
                be.rx_offset = rx.md_rx_offset;
                be.rx_size   = rx.md_rx_size;
                golden_fifo.push_back(be);
            end
        end
    endfunction

    // Para imprimir contribuyentes y armar el golden esperado con los primeros current_size bytes
    typedef struct {
        logic [31:0] rx_data;
        logic [1:0]  rx_offset;
        logic [2:0]  rx_size;
        int          idx_list[$];
        byte unsigned val_list[$];
    } contrib_t;

    function automatic void build_expected_and_contributors(
        output logic [31:0] exp,
        output string contrib
    );
        // *** DECLARACIONES PRIMERO ***
        contrib_t by_seq[int];
        int i, k;
        string s;
        byte_entry_t be;

        // *** SENTENCIAS DESPUÉS ***
        exp     = '0;
        contrib = "";

        for (i = 0; i < current_size; i++) begin
            be = golden_fifo[i];
            exp[8*(current_offset + i) +: 8] = be.value;

            if (!by_seq.exists(be.rx_seq)) begin
                contrib_t t;
                t.rx_data   = be.rx_data;
                t.rx_offset = be.rx_offset;
                t.rx_size   = be.rx_size;
                by_seq[be.rx_seq] = t;
            end
            by_seq[be.rx_seq].idx_list.push_back(be.idx_in_rx);
            by_seq[be.rx_seq].val_list.push_back(be.value);
        end

        s = "";
        foreach (by_seq[seq]) begin
            contrib_t t = by_seq[seq];
            s = {s, $sformatf("(RX#%0d: data=0x%08h, off=%0d, size=%0d, bytes=[",
                              seq, t.rx_data, t.rx_offset, t.rx_size)};
            for (k = 0; k < t.idx_list.size(); k++) begin
                s = {s, $sformatf("%0d:0x%02h", t.idx_list[k], t.val_list[k])};
                if (k < t.idx_list.size()-1) s = {s, ", "};
            end
            s = {s, "]) "};
        end
        contrib = s;
    endfunction

    function automatic void commit_bytes();
        int i;
        for (i = 0; i < current_size; i++) void'(golden_fifo.pop_front());
    endfunction

    function automatic bit has_bytes_pending_for_rx_seq(int seq);
        foreach (golden_fifo[i]) begin
            if (golden_fifo[i].rx_seq == seq) return 1;
        end
        return 0;
    endfunction

    //==============================
    // CHECKS
    //==============================
    function automatic checker_result check_illegal_transfer(
        trans_rx_in rx_trans,
        trans_rx_out rx_resp,
        int rx_seq_id
    );
        checker_result r = new();
        bit legal;

        r.timestamp        = $realtime;
        r.test_description = "Illegal Transfer Detection";
        r.rx_seq_id        = rx_seq_id;
        r.tx_seq_id        = 0;
        r.rx_data          = rx_trans.md_rx_data;
        r.rx_offset        = rx_trans.md_rx_offset;
        r.rx_size          = rx_trans.md_rx_size;
        r.tx_data          = '0;
        r.tx_offset        = '0;
        r.tx_size          = '0;
        r.config_size      = current_size;
        r.config_offset    = current_offset;
        r.golden_expected  = '0;
        r.rx_contributors  = "";

        legal = validate_rx_transfer(rx_trans.md_rx_offset, rx_trans.md_rx_size);

        if (!legal) begin
            if (rx_resp.md_rx_err == 1) begin
                r.test_passed   = 1;
                r.error_message = "Illegal transfer correctly detected";
                illegal_transfers_detected++;
            end else begin
                r.test_passed   = 0;
                r.error_message = $sformatf("Illegal transfer NOT detected (off=%0d,size=%0d)",
                                             rx_trans.md_rx_offset, rx_trans.md_rx_size);
            end
        end else begin
            if (rx_resp.md_rx_err == 0) begin
                r.test_passed   = 1;
                r.error_message = "Legal transfer correctly processed";
            end else begin
                r.test_passed   = 0;
                r.error_message = "Legal transfer flagged as error";
            end
        end
        return r;
    endfunction

    //==============================
    // HILOS
    //==============================
    task monitor_apb_config();
        forever begin
            trans_apb_in apb_trans;
            apb_config_mbx.get(apb_trans);
            if (apb_trans.pwrite && (apb_trans.paddr == 16'h0000)) begin
                logic [2:0] new_size   = apb_trans.pwdata[2:0];
                logic [1:0] new_offset = apb_trans.pwdata[9:8];
                if (new_size inside {1,2,4}) begin
                    current_size   = new_size;
                    current_offset = new_offset;
                    $display("T=%0t [Checker] Configuration updated: SIZE=%0d, OFFSET=%0d",
                             $time, current_size, current_offset);
                end
            end
        end
    endtask

    // RX: reporta solo si el caso queda “cerrado” (ilegal o legal con err=1). Los legales acumulan bytes.
    task check_rx_transfers();
        checker_result r_il;
        forever begin
            trans_rx_in  rx_trans;
            trans_rx_out rx_resp;

            rx_in_mbx.get(rx_trans);
            rx_out_mbx.get(rx_resp);

            rx_seq_counter++;

            legal = validate_rx_transfer(rx_trans.md_rx_offset, rx_trans.md_rx_size);

            if (legal && (rx_resp.md_rx_err == 1'b0)) begin
                rx_item_t it;
                push_rx_bytes_to_golden(rx_trans, rx_seq_counter);
                it.seq = rx_seq_counter;
                it.rx  = rx_trans;
                rx_for_tx_q.push_back(it);
                // no imprimimos ni mandamos al scoreboard (evitar parciales)
            end
            else begin
                r_il = check_illegal_transfer(rx_trans, rx_resp, rx_seq_counter);
                total_checks++;
                if (r_il.test_passed) passed_checks++; else failed_checks++;
                r_il.print("[Checker]");
                chk_scb_mbx.put(r_il);
            end
        end
    endtask

    // TX: cuando hay bytes suficientes arma golden + contributors y emite el resultado.
    task check_tx_transfers();
        checker_result r_tx;
        forever begin
            trans_tx_out tx_trans;
            tx_out_mbx.get(tx_trans);
            tx_seq_counter++;

            if (rx_for_tx_q.size() == 0) begin
                // No hay RX legal previo → resultado completo (error)
                r_tx = new();
                r_tx.timestamp        = $realtime;
                r_tx.test_description = "TX without prior legal RX";
                r_tx.test_passed      = 0;
                r_tx.error_message    = "No matching legal RX in queue";
                r_tx.rx_seq_id        = 0;
                r_tx.tx_seq_id        = tx_seq_counter;
                r_tx.tx_data          = tx_trans.md_tx_data;
                r_tx.tx_offset        = tx_trans.md_tx_offset;
                r_tx.tx_size          = tx_trans.md_tx_size;
                r_tx.config_size      = current_size;
                r_tx.config_offset    = current_offset;
                r_tx.golden_expected  = '0;
                r_tx.rx_contributors  = "";

                total_checks++; failed_checks++;
                r_tx.print("[Checker]");
                chk_scb_mbx.put(r_tx);
                continue;
            end

            // RX “representativo” (para campos RX_* del resultado)
            rx_item_t rx_rep = rx_for_tx_q[0];

            if (golden_fifo.size() < current_size) begin
                r_tx = new();
                r_tx.timestamp        = $realtime;
                r_tx.test_description = "Data Alignment Verification";
                r_tx.rx_seq_id        = rx_rep.seq;
                r_tx.tx_seq_id        = tx_seq_counter;
                r_tx.rx_data          = rx_rep.rx.md_rx_data;
                r_tx.rx_offset        = rx_rep.rx.md_rx_offset;
                r_tx.rx_size          = rx_rep.rx.md_rx_size;
                r_tx.tx_data          = tx_trans.md_tx_data;
                r_tx.tx_offset        = tx_trans.md_tx_offset;
                r_tx.tx_size          = tx_trans.md_tx_size;
                r_tx.config_size      = current_size;
                r_tx.config_offset    = current_offset;
                r_tx.golden_expected  = '0;
                r_tx.rx_contributors  = $sformatf("Bytes disponibles=%0d, requeridos=%0d",
                                                  golden_fifo.size(), current_size);
                r_tx.test_passed   = 0;
                r_tx.error_message = $sformatf("Not enough RX bytes for TX: need %0d, have %0d",
                                               current_size, golden_fifo.size());

                total_checks++; failed_checks++;
                r_tx.print("[Checker]");
                chk_scb_mbx.put(r_tx);
                continue;
            end

            // Construir golden + contributors (con los primeros current_size bytes)
            logic [31:0] expected;
            string contributors;
            build_expected_and_contributors(expected, contributors);

            r_tx = new();
            r_tx.timestamp        = $realtime;
            r_tx.test_description = "Data Alignment Verification";
            r_tx.rx_seq_id        = rx_rep.seq;
            r_tx.tx_seq_id        = tx_seq_counter;

            r_tx.rx_data       = rx_rep.rx.md_rx_data;
            r_tx.rx_offset     = rx_rep.rx.md_rx_offset;
            r_tx.rx_size       = rx_rep.rx.md_rx_size;
            r_tx.tx_data       = tx_trans.md_tx_data;
            r_tx.tx_offset     = tx_trans.md_tx_offset;
            r_tx.tx_size       = tx_trans.md_tx_size;
            r_tx.config_size   = current_size;
            r_tx.config_offset = current_offset;

            r_tx.golden_expected = expected;
            r_tx.rx_contributors = contributors;

            // Checks finales
            if (tx_trans.md_tx_size   != current_size) begin
                r_tx.test_passed = 0;
                r_tx.error_message = $sformatf("TX size mismatch: expected %0d, got %0d",
                                               current_size, tx_trans.md_tx_size);
            end
            else if (tx_trans.md_tx_offset != current_offset) begin
                r_tx.test_passed = 0;
                r_tx.error_message = $sformatf("TX offset mismatch: expected %0d, got %0d",
                                               current_offset, tx_trans.md_tx_offset);
            end
            else if (!tx_trans.md_tx_valid) begin
                r_tx.test_passed = 0;
                r_tx.error_message = "TX valid not asserted";
            end
            else if (expected !== tx_trans.md_tx_data) begin
                r_tx.test_passed = 0;
                r_tx.error_message = $sformatf("TX data mismatch: expected 0x%08h, got 0x%08h",
                                               expected, tx_trans.md_tx_data);
            end
            else begin
                r_tx.test_passed   = 1;
                r_tx.error_message = "Alignment check passed";

                // Consumir bytes usados
                commit_bytes();

                // Limpiar RX ya consumidos (los de la cabeza que ya no aportan bytes)
                while (rx_for_tx_q.size() > 0 &&
                       !has_bytes_pending_for_rx_seq(rx_for_tx_q[0].seq)) begin
                    void'(rx_for_tx_q.pop_front());
                end
            end

            total_checks++; alignment_checks++;
            if (r_tx.test_passed) passed_checks++; else failed_checks++;
            r_tx.print("[Checker]");
            chk_scb_mbx.put(r_tx);
        end
    endtask

    task run();
        $display("T=%0t [Checker] Iniciado", $time);
        fork
            monitor_apb_config();
            check_rx_transfers();
            check_tx_transfers();
        join_none
    endtask

    function void print_statistics();
        real pass_rate;
        $display("========================================");
        $display("       CHECKER STATISTICS");
        $display("========================================");
        $display("Total Checks:              %0d", total_checks);
        $display("Passed Checks:             %0d", passed_checks);
        $display("Failed Checks:             %0d", failed_checks);
        $display("Illegal Transfers Detected: %0d", illegal_transfers_detected);
        $display("Alignment Checks:          %0d", alignment_checks);
        pass_rate = (total_checks>0) ?
            (real'(passed_checks)/real'(total_checks))*100.0 : 0.0;
        $display("Pass Rate:                 %0.2f%%", pass_rate);
        $display("========================================");
    endfunction

endclass
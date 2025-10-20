//================================================================================
// Checker para validar el funcionamiento del Aligner
//================================================================================

//================================================================================
// Clase para reportar resultados al Scoreboard
//================================================================================
class checker_result;
    // Información de la verificación
    bit         test_passed;           // ¿Pasó la prueba?
    string      test_description;      // Descripción
    string      error_message;         // Mensaje (ok/falla)
    realtime    timestamp;             // Momento

    // NUEVO: identificadores de secuencia
    int         rx_seq_id;             // N° de RX usado/checado
    int         tx_seq_id;             // N° de TX usado/checado (0 si no aplica)

    // Datos relevantes
    logic [31:0] rx_data;
    logic [1:0]  rx_offset;
    logic [2:0]  rx_size;
    logic [31:0] tx_data;
    logic [1:0]  tx_offset;
    logic [2:0]  tx_size;
    logic [2:0]  config_size;
    logic [1:0]  config_offset;

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

        // TX (si no aplica, se muestra N/A)
        if (tx_seq_id == 0 && tx_size == 0)
            $display("T=%0t %s TX: N/A (aún no emparejado)", $time, tag);
        else
            $display("T=%0t %s TX: data=0x%08h, offset=%0d, size=%0d",
                     $time, tag, tx_data, tx_offset, tx_size);

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
    localparam int ALGN_DATA_WIDTH = 32;      // ← antes era 'parameter'
    localparam int DATA_BYTES      = ALGN_DATA_WIDTH/8; // 4
    logic [2:0] current_size   = 1; // reset
    logic [1:0] current_offset = 0; // reset

    //==============================
    // COLAS / ESTADÍSTICAS
    //==============================
    byte unsigned golden_fifo[$];   // bytes en orden de llegada

    // Emparejamiento RX↔TX para reportes
    typedef struct {                 // ← antes era 'struct packed'
        int         seq;
        trans_rx_in rx;              // handle de clase permitido en struct *unpacked*
    } rx_item_t;

    rx_item_t rx_for_tx_q[$];       // RX legales pendientes de emparejar con un TX

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
    function bit validate_rx_transfer(logic [1:0] offset, logic [2:0] size);
        if (!(size inside {1,2,4})) return 0;
        return (((DATA_BYTES + offset) % size) == 0);
    endfunction

    function void push_rx_bytes_to_golden(trans_rx_in rx);
        byte unsigned bytes[DATA_BYTES];
        bytes[0] = rx.md_rx_data[7:0];
        bytes[1] = rx.md_rx_data[15:8];
        bytes[2] = rx.md_rx_data[23:16];
        bytes[3] = rx.md_rx_data[31:24];
        for (int i = 0; i < rx.md_rx_size; i++) begin
            int idx = rx.md_rx_offset + i;
            if (idx < DATA_BYTES)
                golden_fifo.push_back(bytes[idx]);
        end
    endfunction

    function logic [31:0] peek_expected_word();
        logic [31:0] w = 32'h0;
        for (int i = 0; i < current_size; i++) begin
            byte unsigned bi = golden_fifo[i];
            w[8*(current_offset + i) +: 8] = bi;
        end
        return w;
    endfunction

    function void commit_bytes();
        for (int i = 0; i < current_size; i++) void'(golden_fifo.pop_front());
    endfunction

    //==============================
    // CHECKS
    //==============================
    function checker_result check_illegal_transfer(
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

    function checker_result check_alignment(
        rx_item_t rx_item,
        trans_tx_out tx_trans,
        int tx_seq_id
    );
        checker_result r = new();
        logic [31:0] expected;
        r.timestamp        = $realtime;
        r.test_description = "Data Alignment Verification";
        r.rx_seq_id        = rx_item.seq;
        r.tx_seq_id        = tx_seq_id;

        r.rx_data       = rx_item.rx.md_rx_data;
        r.rx_offset     = rx_item.rx.md_rx_offset;
        r.rx_size       = rx_item.rx.md_rx_size;
        r.tx_data       = tx_trans.md_tx_data;
        r.tx_offset     = tx_trans.md_tx_offset;
        r.tx_size       = tx_trans.md_tx_size;
        r.config_size   = current_size;
        r.config_offset = current_offset;

        if (tx_trans.md_tx_size   != current_size)  begin
            r.test_passed = 0;
            r.error_message = $sformatf("TX size mismatch: expected %0d, got %0d",
                                        current_size, tx_trans.md_tx_size);
            return r;
        end
        if (tx_trans.md_tx_offset != current_offset) begin
            r.test_passed = 0;
            r.error_message = $sformatf("TX offset mismatch: expected %0d, got %0d",
                                        current_offset, tx_trans.md_tx_offset);
            return r;
        end
        if (!tx_trans.md_tx_valid) begin
            r.test_passed = 0;
            r.error_message = "TX valid not asserted";
            return r;
        end
        if (golden_fifo.size() < current_size) begin
            r.test_passed = 0;
            r.error_message = $sformatf("Not enough RX bytes for TX: need %0d, have %0d",
                                        current_size, golden_fifo.size());
            return r;
        end

        expected = peek_expected_word();
        if (expected !== tx_trans.md_tx_data) begin
            r.test_passed = 0;
            r.error_message = $sformatf("TX data mismatch: expected 0x%08h, got 0x%08h",
                                        expected, tx_trans.md_tx_data);
            return r;
        end

        commit_bytes();
        r.test_passed   = 1;
        r.error_message = "Alignment check passed";
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

    task check_rx_transfers();
        checker_result r_il;
        forever begin
            trans_rx_in  rx_trans;
            trans_rx_out rx_resp;

            rx_in_mbx.get(rx_trans);
            rx_out_mbx.get(rx_resp);

            rx_seq_counter++;

            r_il = check_illegal_transfer(rx_trans, rx_resp, rx_seq_counter);

            if (validate_rx_transfer(rx_trans.md_rx_offset, rx_trans.md_rx_size) &&
                (rx_resp.md_rx_err == 1'b0)) begin
                rx_item_t it;        // declaración antes de usar
                push_rx_bytes_to_golden(rx_trans);
                it.seq = rx_seq_counter;
                it.rx  = rx_trans;
                rx_for_tx_q.push_back(it);
            end

            total_checks++;
            if (r_il.test_passed) passed_checks++; else failed_checks++;
            r_il.print("[Checker]");
            chk_scb_mbx.put(r_il);
        end
    endtask

    task check_tx_transfers();
        checker_result r_tx;
        forever begin
            trans_tx_out tx_trans;
            rx_item_t    rx_item;
            tx_out_mbx.get(tx_trans);
            tx_seq_counter++;

            if (rx_for_tx_q.size() == 0) begin
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

                total_checks++; failed_checks++;
                r_tx.print("[Checker]");
                chk_scb_mbx.put(r_tx);
                continue;
            end

            rx_item = rx_for_tx_q.pop_front();

            r_tx = check_alignment(rx_item, tx_trans, tx_seq_counter);

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
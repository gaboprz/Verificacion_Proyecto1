//================================================================================
// Checker para validar el funcionamiento del Aligner - VERSIÓN MEJORADA
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
// Clase principal del Checker MEJORADA
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

    //==============================
    // ESTRUCTURAS PARA AGRUPAMIENTO
    //==============================
    
    // Estructura para RX items (ya existente)
    typedef struct {
        int         seq;
        trans_rx_in rx;
    } rx_item_t;

    // NUEVA: Estructura para agrupar múltiples RX que forman un TX
    typedef struct {
        int seq_id;
        rx_item_t rx_items[$];      // Todos los RX que contribuyeron
        logic [31:0] expected_data; // Dato esperado del golden reference
        int bytes_required;         // Bytes necesarios para este TX
        int bytes_collected;        // Bytes actualmente recolectados
    } tx_group_t;
    
    tx_group_t pending_tx_groups[$]; // Grupos pendientes de completar
    
    // Colas existentes (se mantienen)
    byte unsigned golden_fifo[$];
    rx_item_t rx_for_tx_q[$];       // Para compatibilidad con sistema antiguo

    // Contadores
    int total_checks = 0;
    int passed_checks = 0;
    int failed_checks = 0;
    int illegal_transfers_detected = 0;
    int alignment_checks = 0;
    int rx_seq_counter = 0;
    int tx_seq_counter = 0;
    int tx_group_counter = 0;

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
            if (i < golden_fifo.size()) begin
                byte unsigned bi = golden_fifo[i];
                w[8*(current_offset + i) +: 8] = bi;
            end
        end
        return w;
    endfunction

    function void commit_bytes();
        for (int i = 0; i < current_size; i++) begin
            if (golden_fifo.size() > 0) begin
                void'(golden_fifo.pop_front());
            end
        end
    endfunction

    //==============================
    // NUEVAS FUNCIONES PARA AGRUPAMIENTO
    //==============================
    
    // Función para crear un nuevo grupo de TX
    function tx_group_t create_new_tx_group();
        tx_group_t group;
        group.seq_id = tx_group_counter++;
        group.bytes_required = current_size;
        group.bytes_collected = 0;
        group.expected_data = 32'h0;
        return group;
    endfunction
    
    // Función para agregar un RX a un grupo existente
    function void add_rx_to_group(ref tx_group_t group, rx_item_t rx_item);
        group.rx_items.push_back(rx_item);
        group.bytes_collected += rx_item.rx.md_rx_size;
    endfunction
    
    // Función para imprimir un grupo completo
    function void print_tx_group(tx_group_t group, trans_tx_out tx_trans, bit test_passed, string error_msg);
        $display("T=%0t [Checker] ============================================", $time);
        $display("T=%0t [Checker] TX GROUP #%0d - COMPLETE ALIGNMENT CHECK", $time, group.seq_id);
        $display("T=%0t [Checker] RESULT: %s", $time, test_passed ? "PASSED" : "FAILED");
        $display("T=%0t [Checker] INFO: %s", $time, error_msg);
        $display("T=%0t [Checker] Config: SIZE=%0d, OFFSET=%0d", $time, current_size, current_offset);
        $display("T=%0t [Checker] Bytes Required: %0d, Bytes Collected: %0d", $time, group.bytes_required, group.bytes_collected);
        $display("T=%0t [Checker] ---", $time);
        
        // Mostrar todos los RX que contribuyeron
        foreach (group.rx_items[i]) begin
            $display("T=%0t [Checker] RX #%0d: data=0x%08h, offset=%0d, size=%0d", 
                     $time, group.rx_items[i].seq, 
                     group.rx_items[i].rx.md_rx_data,
                     group.rx_items[i].rx.md_rx_offset, 
                     group.rx_items[i].rx.md_rx_size);
        end
        
        $display("T=%0t [Checker] ---", $time);
        $display("T=%0t [Checker] GOLDEN REFERENCE: data=0x%08h", $time, group.expected_data);
        $display("T=%0t [Checker] ACTUAL TX: data=0x%08h, offset=%0d, size=%0d", 
                 $time, tx_trans.md_tx_data, tx_trans.md_tx_offset, tx_trans.md_tx_size);
        $display("T=%0t [Checker] ============================================", $time);
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

    // Función de alineamiento ORIGINAL (para compatibilidad)
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

    // NUEVA función para verificación de alineamiento con grupos
    function checker_result check_alignment_with_group(
        tx_group_t group,
        trans_tx_out tx_trans,
        int tx_seq_id
    );
        checker_result r = new();
        logic [31:0] expected;
        r.timestamp        = $realtime;
        r.test_description = "Data Alignment Verification (Grouped)";
        r.rx_seq_id        = (group.rx_items.size() > 0) ? group.rx_items[0].seq : 0;
        r.tx_seq_id        = tx_seq_id;
        r.config_size      = current_size;
        r.config_offset    = current_offset;

        // Usar el primer RX para los datos de referencia
        if (group.rx_items.size() > 0) begin
            r.rx_data   = group.rx_items[0].rx.md_rx_data;
            r.rx_offset = group.rx_items[0].rx.md_rx_offset;
            r.rx_size   = group.rx_items[0].rx.md_rx_size;
        end

        r.tx_data   = tx_trans.md_tx_data;
        r.tx_offset = tx_trans.md_tx_offset;
        r.tx_size   = tx_trans.md_tx_size;

        // Verificaciones (igual que la función original)
        if (tx_trans.md_tx_size != current_size) begin
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

        // Calcular expected_data en el momento de la verificación
        expected = peek_expected_word();
        group.expected_data = expected; // Actualizar el grupo
        
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
    // HILOS MEJORADOS
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
                    
                    // Limpiar grupos pendientes cuando cambia la configuración
                    pending_tx_groups.delete();
                    golden_fifo.delete(); // También limpiar la golden FIFO
                end
            end
        end
    endtask
    bit added_to_existing = 0;
    task check_rx_transfers();
        checker_result r_il;
        forever begin
            trans_rx_in  rx_trans;
            trans_rx_out rx_resp;

            rx_in_mbx.get(rx_trans);
            rx_out_mbx.get(rx_resp);

            rx_seq_counter++;

            // Verificación de legalidad (igual que antes)
            r_il = check_illegal_transfer(rx_trans, rx_resp, rx_seq_counter);

            if (validate_rx_transfer(rx_trans.md_rx_offset, rx_trans.md_rx_size) &&
                (rx_resp.md_rx_err == 1'b0)) begin
                
                rx_item_t rx_item;
                rx_item.seq = rx_seq_counter;
                rx_item.rx  = rx_trans;
                
                push_rx_bytes_to_golden(rx_trans);
                
                // NUEVO: Manejo de grupos
                // Buscar un grupo pendiente que necesite más bytes
                
                foreach (pending_tx_groups[i]) begin
                    if (pending_tx_groups[i].bytes_collected < pending_tx_groups[i].bytes_required) begin
                        add_rx_to_group(pending_tx_groups[i], rx_item);
                        added_to_existing = 1;
                        break;
                    end
                end
                
                // Si no se pudo agregar a grupo existente, crear uno nuevo
                if (!added_to_existing) begin
                    tx_group_t new_group = create_new_tx_group();
                    add_rx_to_group(new_group, rx_item);
                    pending_tx_groups.push_back(new_group);
                end
                
                // Mantener compatibilidad con el sistema antiguo
                rx_for_tx_q.push_back(rx_item);
            end

            // Solo imprimir checks de illegal transfers inmediatamente
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
            tx_out_mbx.get(tx_trans);
            tx_seq_counter++;

            // PRIMERO: Buscar un grupo completo que coincida (NUEVO SISTEMA)
            tx_group_t matching_group;
            int group_index = -1;
            
            foreach (pending_tx_groups[i]) begin
                if (pending_tx_groups[i].bytes_collected >= pending_tx_groups[i].bytes_required) begin
                    matching_group = pending_tx_groups[i];
                    group_index = i;
                    break;
                end
            end
            
            if (group_index != -1) begin
                // Usar el NUEVO sistema con grupos
                pending_tx_groups.delete(group_index);
                r_tx = check_alignment_with_group(matching_group, tx_trans, tx_seq_counter);
                
                // IMPRIMIR GRUPO COMPLETO
                print_tx_group(matching_group, tx_trans, r_tx.test_passed, r_tx.error_message);
                
            end else begin
                // FALLBACK: Sistema antiguo (para compatibilidad)
                rx_item_t rx_item;
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
                r_tx.print("[Checker]"); // Imprimir también los casos del sistema antiguo
            end

            total_checks++; 
            alignment_checks++;
            if (r_tx.test_passed) passed_checks++; else failed_checks++;
            
            // Enviar al scoreboard
            chk_scb_mbx.put(r_tx);
        end
    endtask

    task run();
        $display("T=%0t [Checker] Iniciado con agrupamiento mejorado", $time);
        fork
            monitor_apb_config();
            check_rx_transfers();
            check_tx_transfers();
        join_none
    endtask

    function void print_statistics();
        real pass_rate;
        $display("========================================");
        $display("       CHECKER STATISTICS (MEJORADO)");
        $display("========================================");
        $display("Total Checks:              %0d", total_checks);
        $display("Passed Checks:             %0d", passed_checks);
        $display("Failed Checks:             %0d", failed_checks);
        $display("Illegal Transfers Detected: %0d", illegal_transfers_detected);
        $display("Alignment Checks:          %0d", alignment_checks);
        $display("TX Groups Processed:       %0d", tx_group_counter);
        $display("Pending TX Groups:         %0d", pending_tx_groups.size());
        pass_rate = (total_checks>0) ?
            (real'(passed_checks)/real'(total_checks))*100.0 : 0.0;
        $display("Pass Rate:                 %0.2f%%", pass_rate);
        $display("========================================");
    endfunction

endclass
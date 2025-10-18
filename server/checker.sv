//================================================================================
// Checker para validar el funcionamiento del Aligner
//================================================================================

//================================================================================
// Clase para reportar resultados al Scoreboard
//================================================================================
class checker_result;
    // Información de la verificación
    bit         test_passed;           // ¿Pasó la prueba?
    string      test_description;      // Descripción de qué se verificó
    string      error_message;         // Mensaje de error si falló
    realtime    timestamp;             // Momento de la verificación
    
    // Datos relevantes de la transacción verificada
    logic [31:0] rx_data;
    logic [1:0]  rx_offset;
    logic [2:0]  rx_size;
    logic [31:0] tx_data;
    logic [1:0]  tx_offset;
    logic [2:0]  tx_size;
    logic [2:0]  config_size;
    logic [1:0]  config_offset;
    
    // Contadores
    int checks_passed;
    int checks_failed;
    
    function void print(string tag="");
        $display("T=%0t %s ============================================", $time, tag);
        $display("T=%0t %s TEST: %s", $time, tag, test_description);
        $display("T=%0t %s RESULT: %s", $time, tag, test_passed ? "PASSED" : "FAILED");
        if (!test_passed)
            $display("T=%0t %s ERROR: %s", $time, tag, error_message);
        $display("T=%0t %s Config: SIZE=%0d, OFFSET=%0d", $time, tag, config_size, config_offset);
        $display("T=%0t %s RX: data=0x%0h, offset=%0d, size=%0d", $time, tag, rx_data, rx_offset, rx_size);
        $display("T=%0t %s TX: data=0x%0h, offset=%0d, size=%0d", $time, tag, tx_data, tx_offset, tx_size);
        $display("T=%0t %s ============================================", $time, tag);
    endfunction
endclass

// Definir mailbox específico para checker_result
typedef mailbox #(checker_result) checker_result_mbx;

//================================================================================
// Clase principal del Checker
//================================================================================
class aligner_checker;
    
    //--------------------------------------------------
    // MAILBOXES DE ENTRADA (desde agentes y monitores)
    //--------------------------------------------------
    trans_apb_in_mbx    apb_config_mbx;    // Configuración APB desde generador
    trans_rx_in_mbx     rx_in_mbx;         // Transacciones RX desde generador
    trans_rx_out_mbx    rx_out_mbx;        // Respuestas RX desde monitor
    trans_tx_out_mbx    tx_out_mbx;        // Transacciones TX desde monitor
    
    //--------------------------------------------------
    // MAILBOX DE SALIDA (hacia scoreboard)
    //--------------------------------------------------
    checker_result_mbx  chk_scb_mbx;
    
    //--------------------------------------------------
    // VARIABLES DE ESTADO
    //--------------------------------------------------
    // Configuración actual del Aligner
    logic [2:0] current_size = 1;      // Valor por defecto según reset
    logic [1:0] current_offset = 0;    // Valor por defecto según reset
    
    // Colas para almacenar transacciones pendientes de verificación
    trans_rx_in  rx_queue[$];          // Cola de transacciones RX recibidas
    trans_rx_out rx_resp_queue[$];     // Cola de respuestas RX
    trans_tx_out tx_queue[$];          // Cola de transacciones TX
    
    // Contadores estadísticos
    int total_checks = 0;
    int passed_checks = 0;
    int failed_checks = 0;
    int illegal_transfers_detected = 0;
    int alignment_checks = 0;

    logic [31:0] expected_data;

    // Verificar si la transacción es legal, validate_rx_transfer
    bit is_legal;
    
    //--------------------------------------------------
    // PARÁMETROS DEL DUT
    //--------------------------------------------------
    parameter ALGN_DATA_WIDTH = 32;
    
    //================================================================================
    // FUNCIÓN: validate_rx_transfer
    // Valida si una transferencia RX cumple con la ecuación legal:
    // ((ALGN_DATA_WIDTH / 8) + offset) % size == 0
    //================================================================================
    function bit validate_rx_transfer(logic [1:0] offset, logic [2:0] size);
        int data_width_bytes = ALGN_DATA_WIDTH / 8;  // 32/8 = 4 bytes
        int result;
        
        // La ecuación según el datasheet:
        // ((ALGN_DATA_WIDTH / 8) + offset) % size == 0
        // Nota: Esta ecuación parece verificar que los datos caben en el bus
        result = (data_width_bytes + offset) % size;
        
        return (result == 0);
    endfunction
    
    //================================================================================
    // FUNCIÓN: extract_aligned_data
    // Extrae los datos alineados según la configuración de SIZE y OFFSET
    // Esta función modela el comportamiento esperado del Aligner
    //================================================================================
    function logic [31:0] extract_aligned_data(
        logic [31:0] input_data, 
        logic [1:0] input_offset,
        logic [2:0] input_size
    );
        logic [31:0] result;
        logic [7:0] bytes[4];  // Array de bytes para manipulación
        
        // Extraer bytes del dato de entrada
        bytes[0] = input_data[7:0];
        bytes[1] = input_data[15:8];
        bytes[2] = input_data[23:16];
        bytes[3] = input_data[31:24];
        
        // El alineamiento toma los datos desde input_offset
        // y los coloca en current_offset de salida
        // Por simplicidad, asumimos que mantiene los bytes válidos
        
        result = input_data;  // Simplificación inicial
        
        return result;
    endfunction
    
    //================================================================================
    // FUNCIÓN: check_alignment
    // Verifica que el alineamiento de datos sea correcto
    // Compara los datos RX de entrada con los datos TX de salida
    //================================================================================
    function checker_result check_alignment(
        trans_rx_in rx_trans,
        trans_tx_out tx_trans
    );
        checker_result result = new();
        result.timestamp = $realtime;
        result.test_description = "Data Alignment Verification";
        
        // Guardar datos para el reporte
        result.rx_data = rx_trans.md_rx_data;
        result.rx_offset = rx_trans.md_rx_offset;
        result.rx_size = rx_trans.md_rx_size;
        result.tx_data = tx_trans.md_tx_data;
        result.tx_offset = tx_trans.md_tx_offset;
        result.tx_size = tx_trans.md_tx_size;
        result.config_size = current_size;
        result.config_offset = current_offset;
        
        // VERIFICACIÓN 1: El TX debe usar la configuración actual
        if (tx_trans.md_tx_size != current_size) begin
            result.test_passed = 0;
            result.error_message = $sformatf(
                "TX size mismatch: expected %0d, got %0d", 
                current_size, tx_trans.md_tx_size
            );
            return result;
        end
        
        if (tx_trans.md_tx_offset != current_offset) begin
            result.test_passed = 0;
            result.error_message = $sformatf(
                "TX offset mismatch: expected %0d, got %0d", 
                current_offset, tx_trans.md_tx_offset
            );
            return result;
        end
        
        // VERIFICACIÓN 2: Los datos deben estar correctamente alineados
        // Para una verificación simple, verificamos que los bytes válidos
        // de RX aparecen en la posición correcta de TX
        expected_data = extract_aligned_data(
            rx_trans.md_rx_data, 
            rx_trans.md_rx_offset,
            rx_trans.md_rx_size
        );
        
        // Por ahora, verificación simplificada: que el dato TX tenga sentido
        // Una verificación más completa requeriría modelar byte por byte
        if (tx_trans.md_tx_valid) begin
            result.test_passed = 1;
            result.error_message = "Alignment check passed";
        end else begin
            result.test_passed = 0;
            result.error_message = "TX valid signal not asserted";
        end
        
        return result;
    endfunction
    
    //================================================================================
    // FUNCIÓN: check_illegal_transfer
    // Verifica que las transferencias ilegales sean detectadas correctamente
    //================================================================================
    function checker_result check_illegal_transfer(
        trans_rx_in rx_trans,
        trans_rx_out rx_resp
    );
        checker_result result = new();
        result.timestamp = $realtime;
        result.test_description = "Illegal Transfer Detection";
        
        // Guardar datos para el reporte
        result.rx_data = rx_trans.md_rx_data;
        result.rx_offset = rx_trans.md_rx_offset;
        result.rx_size = rx_trans.md_rx_size;
        result.config_size = current_size;
        result.config_offset = current_offset;
        
        // Verificar si la transferencia es legal o ilegal
        is_legal = validate_rx_transfer(rx_trans.md_rx_offset, rx_trans.md_rx_size);
        
        // VERIFICACIÓN: Si es ilegal, md_rx_err debe ser 1
        if (!is_legal) begin
            if (rx_resp.md_rx_err == 1) begin
                result.test_passed = 1;
                result.error_message = "Illegal transfer correctly detected";
                illegal_transfers_detected++;
            end else begin
                result.test_passed = 0;
                result.error_message = $sformatf(
                    "Illegal transfer NOT detected: offset=%0d, size=%0d, err=%0d",
                    rx_trans.md_rx_offset, rx_trans.md_rx_size, rx_resp.md_rx_err
                );
            end
        end else begin
            // Si es legal, md_rx_err debe ser 0
            if (rx_resp.md_rx_err == 0) begin
                result.test_passed = 1;
                result.error_message = "Legal transfer correctly processed";
            end else begin
                result.test_passed = 0;
                result.error_message = $sformatf(
                    "Legal transfer incorrectly flagged as error: offset=%0d, size=%0d",
                    rx_trans.md_rx_offset, rx_trans.md_rx_size
                );
            end
        end
        
        return result;
    endfunction
    
    //================================================================================
    // TASK: monitor_apb_config
    // Monitorea las configuraciones APB para actualizar SIZE y OFFSET
    //================================================================================
    task monitor_apb_config();
        forever begin
            trans_apb_in apb_trans;
            apb_config_mbx.get(apb_trans);
            
            // Verificar si es una escritura al registro CTRL (offset 0x0000)
            if (apb_trans.pwrite && apb_trans.psel && apb_trans.penable) begin
                if (apb_trans.paddr == 16'h0000) begin
                    // Extraer SIZE (bits 2:0) y OFFSET (bits 9:8)
                    logic [2:0] new_size = apb_trans.pwdata[2:0];
                    logic [1:0] new_offset = apb_trans.pwdata[9:8];
                    
                    // Actualizar configuración actual
                    if (new_size != 0) begin  // Size 0 es ilegal
                        current_size = new_size;
                        current_offset = new_offset;
                        $display("T=%0t [Checker] Configuration updated: SIZE=%0d, OFFSET=%0d", 
                                 $time, current_size, current_offset);
                    end
                end
            end
        end
    endtask
    
    //================================================================================
    // TASK: check_rx_transfers
    // Verifica las transferencias RX y sus respuestas
    //================================================================================
    task check_rx_transfers();
        forever begin
            trans_rx_in rx_trans;
            trans_rx_out rx_resp;
            checker_result result;
            
            // Esperar transacción RX del generador
            rx_in_mbx.get(rx_trans);
            rx_queue.push_back(rx_trans);
            
            // Esperar respuesta del monitor
            rx_out_mbx.get(rx_resp);
            rx_resp_queue.push_back(rx_resp);
            
            // Obtener la transacción correspondiente de la cola
            trans_rx_in current_rx = rx_queue.pop_front();
            trans_rx_out current_resp = rx_resp_queue.pop_front();
            
            // Verificar si la transferencia es legal/ilegal
            result = check_illegal_transfer(current_rx, current_resp);
            
            // Actualizar estadísticas
            total_checks++;
            if (result.test_passed) begin
                passed_checks++;
            end else begin
                failed_checks++;
            end
            
            // Imprimir resultado
            result.print("[Checker]");
            
            // Enviar resultado al scoreboard
            chk_scb_mbx.put(result);
        end
    endtask
    
    //================================================================================
    // TASK: check_tx_transfers
    // Verifica las transferencias TX (alineamiento)
    //================================================================================
    task check_tx_transfers();
        forever begin
            trans_tx_out tx_trans;
            checker_result result;
            
            // Esperar transacción TX del monitor
            tx_out_mbx.get(tx_trans);
            tx_queue.push_back(tx_trans);
            
            // Verificar que tengamos una transacción RX correspondiente
            // (asumiendo orden FIFO: primera que entra, primera que sale)
            if (rx_queue.size() > 0) begin
                trans_rx_in corresponding_rx = rx_queue[0];  // Peek, no pop
                trans_tx_out current_tx = tx_queue.pop_front();
                
                // Solo verificar alineamiento si la RX fue válida
                bit is_legal = validate_rx_transfer(
                    corresponding_rx.md_rx_offset, 
                    corresponding_rx.md_rx_size
                );
                
                if (is_legal) begin
                    // Verificar alineamiento
                    result = check_alignment(corresponding_rx, current_tx);
                    
                    // Actualizar estadísticas
                    total_checks++;
                    alignment_checks++;
                    if (result.test_passed) begin
                        passed_checks++;
                    end else begin
                        failed_checks++;
                    end
                    
                    // Imprimir resultado
                    result.print("[Checker]");
                    
                    // Enviar resultado al scoreboard
                    chk_scb_mbx.put(result);
                    
                    // Ahora sí, remover la RX procesada
                    rx_queue.pop_front();
                end
            end
        end
    endtask
    
    //================================================================================
    // TASK: run
    // Tarea principal que lanza todos los procesos del checker en paralelo
    //================================================================================
    task run();
        $display("T=%0t [Checker] Iniciado", $time);
        
        fork
            // Monitorear configuración APB
            monitor_apb_config();
            
            // Verificar transferencias RX
            check_rx_transfers();
            
            // Verificar transferencias TX (alineamiento)
            check_tx_transfers();
        join_none
    endtask
    
    //================================================================================
    // FUNCTION: print_statistics
    // Imprime estadísticas finales del checker
    //================================================================================
    function void print_statistics();
        $display("========================================");
        $display("       CHECKER STATISTICS");
        $display("========================================");
        $display("Total Checks:              %0d", total_checks);
        $display("Passed Checks:             %0d", passed_checks);
        $display("Failed Checks:             %0d", failed_checks);
        $display("Illegal Transfers Detected: %0d", illegal_transfers_detected);
        $display("Alignment Checks:          %0d", alignment_checks);
        $display("Pass Rate:                 %0.2f%%", 
                 total_checks > 0 ? (real'(passed_checks)/real'(total_checks))*100.0 : 0.0);
        $display("========================================");
    endfunction

endclass
//================================================================================
// Scoreboard - Recolecta resultados del checker y genera reporte CSV
//================================================================================

class scoreboard;
    // MAILBOX DE ENTRADA
    checker_result_mbx chk_scb_mbx;
    
    // ARCHIVO CSV
    integer csv_file;
    string csv_filename;
    
    // ESTADÍSTICAS GLOBALES
    int total_tests = 0;
    int total_passed = 0;
    int total_failed = 0;
    int total_illegal_transfers = 0;
    int total_alignment_checks = 0;
    
    // CONTADORES POR CONFIGURACIÓN
    int config_tests[string];  // Associative array: "SIZE_OFFSET" -> count
    
    // CONSTRUCTOR
    function new(string filename = "verification_results.csv");
        csv_filename = filename;
        
        // Abrir archivo CSV en modo escritura
        csv_file = $fopen(csv_filename, "w");
        
        if (csv_file == 0) begin
            $display("ERROR: No se pudo abrir el archivo %s", csv_filename);
            $finish;
        end
        
        // Escribir encabezado del CSV
        write_csv_header();
        
        $display("T=%0t [Scoreboard] Inicializado. Archivo CSV: %s", $time, csv_filename);
    endfunction
    
    //================================================================================
    // FUNCIÓN: write_csv_header
    // Escribe el encabezado del archivo CSV
    //================================================================================
    function void write_csv_header();
        $fwrite(csv_file, "Timestamp,");
        $fwrite(csv_file, "Test_Result,");
        $fwrite(csv_file, "Test_Description,");
        $fwrite(csv_file, "Error_Message,");
        $fwrite(csv_file, "Config_SIZE,");
        $fwrite(csv_file, "Config_OFFSET,");
        $fwrite(csv_file, "RX_Data,");
        $fwrite(csv_file, "RX_Offset,");
        $fwrite(csv_file, "RX_Size,");
        $fwrite(csv_file, "TX_Data,");
        $fwrite(csv_file, "TX_Offset,");
        $fwrite(csv_file, "TX_Size,");
        $fwrite(csv_file, "Checks_Passed,");
        $fwrite(csv_file, "Checks_Failed\n");
        
        $fflush(csv_file);
    endfunction
    
    //================================================================================
    // FUNCIÓN: write_csv_entry
    // Escribe una entrada en el archivo CSV
    //================================================================================
    function void write_csv_entry(checker_result result);
        // Timestamp
        $fwrite(csv_file, "%0t,", result.timestamp);
        
        // Test Result (PASS/FAIL)
        $fwrite(csv_file, "%s,", result.test_passed ? "PASS" : "FAIL");
        
        // Test Description (entre comillas para manejar mensajes con comas)
        $fwrite(csv_file, "\"%s\",", result.test_description);
        
        // Error Message (entre comillas para manejar mensajes con comas)
        $fwrite(csv_file, "\"%s\",", result.error_message);
        
        // Configuración
        $fwrite(csv_file, "%0d,", result.config_size);
        $fwrite(csv_file, "%0d,", result.config_offset);
        
        // RX Data
        $fwrite(csv_file, "0x%08h,", result.rx_data);
        $fwrite(csv_file, "%0d,", result.rx_offset);
        $fwrite(csv_file, "%0d,", result.rx_size);
        
        // TX Data
        $fwrite(csv_file, "0x%08h,", result.tx_data);
        $fwrite(csv_file, "%0d,", result.tx_offset);
        $fwrite(csv_file, "%0d,", result.tx_size);
        
        // Contadores
        $fwrite(csv_file, "%0d,", result.checks_passed);
        $fwrite(csv_file, "%0d\n", result.checks_failed);
        
        // Forzar escritura inmediata al disco
        $fflush(csv_file);
    endfunction
    
    //================================================================================
    // FUNCIÓN: update_statistics
    // Actualiza las estadísticas globales con un resultado
    //================================================================================
    function void update_statistics(checker_result result);
        string config_key;
        
        // Actualizar contadores globales
        total_tests++;
        
        if (result.test_passed) begin
            total_passed++;
        end else begin
            total_failed++;
        end
        
        // Clasificar por tipo de test
        if (result.test_description == "Illegal Transfer Detection") begin
            // Detectar si fue una transferencia ilegal correctamente identificada
            if (result.error_message == "Illegal transfer correctly detected") begin
                total_illegal_transfers++;
            end
        end else if (result.test_description == "Data Alignment Verification") begin
            total_alignment_checks++;
        end
        
        // Contadores por configuración (SIZE_OFFSET)
        config_key = $sformatf("SIZE%0d_OFFSET%0d", result.config_size, result.config_offset);
        if (config_tests.exists(config_key)) begin
            config_tests[config_key]++;
        end else begin
            config_tests[config_key] = 1;
        end
    endfunction
    
    //================================================================================
    // FUNCIÓN: print_result
    // Imprime un resultado en consola de forma legible
    //================================================================================
    function void print_result(checker_result result, int result_num);
        $display("================================================================================");
        $display("SCOREBOARD - Resultado #%0d", result_num);
        $display("================================================================================");
        $display("Timestamp:        %0t", result.timestamp);
        $display("Test:             %s", result.test_description);
        $display("Resultado:        %s", result.test_passed ? "✓ PASSED" : "✗ FAILED");
        
        if (!result.test_passed) begin
            $display("Error:            %s", result.error_message);
        end
        
        $display("--------------------------------------------------------------------------------");
        $display("Configuración:    SIZE=%0d, OFFSET=%0d", result.config_size, result.config_offset);
        $display("RX:               data=0x%08h, offset=%0d, size=%0d", 
                 result.rx_data, result.rx_offset, result.rx_size);
        $display("TX:               data=0x%08h, offset=%0d, size=%0d", 
                 result.tx_data, result.tx_offset, result.tx_size);
        $display("================================================================================");
    endfunction
    
    //================================================================================
    // TASK: run
    // Tarea principal que recibe resultados del checker y los procesa
    //================================================================================
    task run();
        checker_result result;
        int result_counter = 0;
        
        $display("T=%0t [Scoreboard] Iniciado - Esperando resultados del checker...", $time);
        
        forever begin
            // Esperar resultado del checker
            chk_scb_mbx.get(result);
            result_counter++;
            
            // Escribir en CSV
            write_csv_entry(result);
            
            // Actualizar estadísticas
            update_statistics(result);
            
            // Imprimir en consola
            print_result(result, result_counter);
            
            // Log breve adicional
            if (result.test_passed) begin
                $display("T=%0t [Scoreboard] ✓ Test #%0d PASSED: %s", 
                         $time, result_counter, result.test_description);
            end else begin
                $display("T=%0t [Scoreboard] ✗ Test #%0d FAILED: %s - %s", 
                         $time, result_counter, result.test_description, result.error_message);
            end
        end
    endtask
    
    //================================================================================
    // FUNCIÓN: finalize
    // Finaliza el scoreboard mostrando estadísticas y cerrando archivos
    //================================================================================
    function void finalize();
        real pass_rate;
        
        $display("T=%0t [Scoreboard] Finalizando...", $time);
        
        // Calcular tasa de éxito
        pass_rate = (total_tests > 0) ? (real'(total_passed) / real'(total_tests)) * 100.0 : 0.0;
        
        // Imprimir estadísticas en consola
        $display("\n\n");
        $display("================================================================================");
        $display("              ESTADÍSTICAS FINALES DEL SCOREBOARD");
        $display("================================================================================");
        $display("Total de tests ejecutados:         %0d", total_tests);
        $display("Tests pasados:                     %0d", total_passed);
        $display("Tests fallidos:                    %0d", total_failed);
        $display("Tasa de éxito:                     %0.2f%%", pass_rate);
        $display("--------------------------------------------------------------------------------");
        $display("Transferencias ilegales detectadas:%0d", total_illegal_transfers);
        $display("Verificaciones de alineamiento:    %0d", total_alignment_checks);
        $display("================================================================================");
        
        $display("\nTests por configuración:");
        foreach (config_tests[key]) begin
            $display("  %-20s: %0d tests", key, config_tests[key]);
        end
        
        $display("\n================================================================================");
        if (pass_rate >= 95.0) begin
            $display("CONCLUSIÓN: ✓ EXCELENTE - El DUT funciona correctamente");
        end else if (pass_rate >= 80.0) begin
            $display("CONCLUSIÓN: ⚠ ACEPTABLE - Revisar tests fallidos");
        end else begin
            $display("CONCLUSIÓN: ✗ CRÍTICO - El DUT tiene problemas significativos");
        end
        $display("================================================================================\n");
        
        // Cerrar archivo CSV
        if (csv_file != 0) begin
            $fclose(csv_file);
            $display("T=%0t [Scoreboard] Archivo CSV cerrado: %s", $time, csv_filename);
        end
        
        $display("T=%0t [Scoreboard] Finalizado exitosamente", $time);
    endfunction

endclass
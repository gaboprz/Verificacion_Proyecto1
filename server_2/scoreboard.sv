//================================================================================
// Scoreboard - Recolecta resultados del checker y genera reporte CSV
//================================================================================
class scoreboard;
    checker_result_mbx chk_scb_mbx;

    integer csv_file;
    string  csv_filename;

    int total_tests = 0;
    int total_passed = 0;
    int total_failed = 0;
    int total_illegal_transfers = 0;
    int total_alignment_checks = 0;

    int config_tests[string];  // "SIZEx_OFFSETy" -> count

    function new(string filename = "verification_results.csv");
        csv_filename = filename;
        csv_file = $fopen(csv_filename, "w");
        if (csv_file == 0) begin
            $display("ERROR: No se pudo abrir el archivo %s", csv_filename);
            $finish;
        end
        write_csv_header();
        $display("T=%0t [Scoreboard] Inicializado. Archivo CSV: %s", $time, csv_filename);
    endfunction

    function void write_csv_header();
        $fwrite(csv_file, "Timestamp,");
        $fwrite(csv_file, "Test_Result,");
        $fwrite(csv_file, "Test_Description,");
        $fwrite(csv_file, "Error_Message,");
        $fwrite(csv_file, "RX_Seq,TX_Seq,");
        $fwrite(csv_file, "Config_SIZE,");
        $fwrite(csv_file, "Config_OFFSET,");
        $fwrite(csv_file, "RX_Data,");
        $fwrite(csv_file, "RX_Offset,");
        $fwrite(csv_file, "RX_Size,");
        $fwrite(csv_file, "TX_Data,");
        $fwrite(csv_file, "TX_Offset,");
        $fwrite(csv_file, "TX_Size,");
        $fwrite(csv_file, "Checks_Passed,");
        $fwrite(csv_file, "Checks_Failed,");
        $fwrite(csv_file, "Golden_Expected,");
        $fwrite(csv_file, "RX_Contributors\n");
        $fflush(csv_file);
    endfunction

    function void write_csv_entry(checker_result result);
        $fwrite(csv_file, "%0t,", result.timestamp);
        $fwrite(csv_file, "%s,", result.test_passed ? "PASS" : "FAIL");
        $fwrite(csv_file, "\"%s\",", result.test_description);
        $fwrite(csv_file, "\"%s\",", result.error_message);

        $fwrite(csv_file, "%0d,", result.rx_seq_id);
        $fwrite(csv_file, "%0d,", result.tx_seq_id);

        $fwrite(csv_file, "%0d,", result.config_size);
        $fwrite(csv_file, "%0d,", result.config_offset);

        $fwrite(csv_file, "0x%08h,", result.rx_data);
        $fwrite(csv_file, "%0d,", result.rx_offset);
        $fwrite(csv_file, "%0d,", result.rx_size);

        if (result.tx_seq_id == 0 && result.tx_size == 0) begin
            $fwrite(csv_file, "NA,NA,NA,");
        end else begin
            $fwrite(csv_file, "0x%08h,", result.tx_data);
            $fwrite(csv_file, "%0d,",   result.tx_offset);
            $fwrite(csv_file, "%0d,",   result.tx_size);
        end

        $fwrite(csv_file, "%0d,", result.checks_passed);
        $fwrite(csv_file, "%0d,", result.checks_failed);
        $fwrite(csv_file, "0x%08h,", result.golden_expected);
        $fwrite(csv_file, "\"%s\"\n", result.rx_contributors);
        $fflush(csv_file);
    endfunction

    function void update_statistics(checker_result result);
        string config_key;
        total_tests++;
        if (result.test_passed) total_passed++; else total_failed++;

        if (result.test_description == "Illegal Transfer Detection") begin
            if (result.error_message == "Illegal transfer correctly detected")
                total_illegal_transfers++;
        end else if (result.test_description == "Data Alignment Verification") begin
            total_alignment_checks++;
        end

        config_key = $sformatf("SIZE%0d_OFFSET%0d", result.config_size, result.config_offset);
        if (config_tests.exists(config_key)) config_tests[config_key]++;
        else config_tests[config_key] = 1;
    endfunction

    function void print_result(checker_result result, int result_num);
        $display("================================================================================");
        $display("SCOREBOARD - Resultado #%0d", result_num);
        $display("================================================================================");
        $display("Timestamp:        %0t", result.timestamp);
        $display("Test:             %s", result.test_description);
        $display("Resultado:        %s", result.test_passed ? "✓ PASSED" : "✗ FAILED");
        $display("Secuencias:       RX=%0d  TX=%0d", result.rx_seq_id, result.tx_seq_id);
        if (!result.test_passed) $display("Error:            %s", result.error_message);
        $display("--------------------------------------------------------------------------------");
        $display("Config:           SIZE=%0d, OFFSET=%0d", result.config_size, result.config_offset);
        $display("RX:               data=0x%08h, offset=%0d, size=%0d",
                 result.rx_data, result.rx_offset, result.rx_size);
        if (!(result.tx_seq_id == 0 && result.tx_size == 0)) begin
            $display("TX:               data=0x%08h, offset=%0d, size=%0d",
                     result.tx_data, result.tx_offset, result.tx_size);
            $display("Contribuyentes RX: %s", result.rx_contributors);
            $display("Golden esperado:   0x%08h", result.golden_expected);
        end
        $display("================================================================================");
    endfunction

    task run();
        checker_result result;
        int result_counter;
        result_counter = 0;
        $display("T=%0t [Scoreboard] Iniciado - Esperando resultados del checker...", $time);
        forever begin
            chk_scb_mbx.get(result);
            result_counter++;
            write_csv_entry(result);
            update_statistics(result);
            print_result(result, result_counter);

            if (result.test_passed)
                $display("T=%0t [Scoreboard] ✓ Test #%0d PASSED: %s",
                         $time, result_counter, result.test_description);
            else
                $display("T=%0t [Scoreboard] ✗ Test #%0d FAILED: %s - %s",
                         $time, result_counter, result.test_description, result.error_message);
        end
    endtask

    function void finalize();
        real pass_rate;
        pass_rate = (total_tests > 0) ? (real'(total_passed) / real'(total_tests)) * 100.0 : 0.0;

        $display("T=%0t [Scoreboard] Finalizando...", $time);
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
        if (pass_rate >= 95.0)
            $display("CONCLUSIÓN: ✓ EXCELENTE - El DUT funciona correctamente");
        else if (pass_rate >= 80.0)
            $display("CONCLUSIÓN: ⚠ ACEPTABLE - Revisar tests fallidos");
        else
            $display("CONCLUSIÓN: ✗ CRÍTICO - El DUT tiene problemas significativos");
        $display("================================================================================\n");

        if (csv_file != 0) begin
            $fclose(csv_file);
            $display("T=%0t [Scoreboard] Archivo CSV cerrado: %s", $time, csv_filename);
        end
        $display("T=%0t [Scoreboard] Finalizado exitosamente", $time);
    endfunction
endclass
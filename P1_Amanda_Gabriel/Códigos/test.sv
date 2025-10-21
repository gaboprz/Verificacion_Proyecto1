//================================================================================
// Archivo del test del ambiente de pruebas 
//================================================================================

// Se incluyen archivos necesarios
`include "env.sv"

class test;
  // Mailboxes con MB_RX
  comando_test_agente_MD_RX_mbx     md_rx_test_agt_mbx;
  num_trans_test_agente_MD_RX_mbx   md_rx_test_agt_num_tran_mbx;

  // Instrucciones del test al agente de MB_RX
  instr_agente_MD_RX                md_rx_tipo_instr;
  cantidad_inst_agente_MD_RX        md_rx_cant_instr;
  //--------------------------------------------------
  // MAILBOXES Y CONFIGURACIÓN MD_TX
  //--------------------------------------------------
  comando_test_agente_MD_TX_mbx     md_tx_test_agt_instruccion_tx;
  num_trans_test_agente_MD_TX_mbx   md_tx_test_agt_num_trans_tx;
  instr_agente_MD_TX                md_tx_tipo_instr;
  cantidad_inst_agente_MD_TX        md_tx_cant_instr;

  //--------------------------------------------------
  // MAILBOXES Y CONFIGURACIÓN APB
  //--------------------------------------------------
  comando_test_agente_APB_mbx       apb_test_agt_mbx;
  num_trans_test_agente_APB_mbx     apb_test_agt_num_tran_mbx;
  instr_agente_APB                  apb_tipo_instr;
  cantidad_inst_agente_APB          apb_cant_instr;

  // Definición del ambiente de prueba
  env e0;

  // Definición de interfaces
  virtual md_rx_interface md_rx_vif;
  virtual md_tx_interface md_tx_vif;
  virtual apb_interface   apb_vif;

function new();
        // Instanciación de mailboxes
        md_rx_test_agt_mbx          = new();
        md_rx_test_agt_num_tran_mbx = new();
        md_tx_test_agt_instruccion_tx = new();
        md_tx_test_agt_num_trans_tx   = new();
        apb_test_agt_mbx            = new();
        apb_test_agt_num_tran_mbx   = new();

        // Crear environment
        e0 = new();
        
        $display("T=%0t [Test] Test creado", $time);
    endfunction
  
    task run();
        $display("T=%0t [Test] Test inicializado", $time);

        // Asignación de interfaces
        e0.md_rx_vif = md_rx_vif;
        e0.md_tx_vif = md_tx_vif;
        e0.apb_vif   = apb_vif;

        // Verificar asignación
        if (e0.md_rx_vif == null) begin
            $display("ERROR: e0.md_rx_vif es null en test");
            $finish;
        end
        if (e0.md_tx_vif == null) begin
            $display("ERROR: e0.md_tx_vif es null en test");
            $finish;
        end
        if (e0.apb_vif == null) begin
            $display("ERROR: e0.apb_vif es null en test");
            $finish;
        end

        // Conectar mailboxes del test al environment
        e0.md_rx_test_agt_mbx = md_rx_test_agt_mbx;
        e0.md_rx_agent_0.test_agt_mbx = md_rx_test_agt_mbx;
        e0.md_rx_test_agt_num_tran_mbx = md_rx_test_agt_num_tran_mbx;
        e0.md_rx_agent_0.test_agt_num_tran_mbx = md_rx_test_agt_num_tran_mbx;

        e0.md_tx_test_agt_instruccion_tx = md_tx_test_agt_instruccion_tx;
        e0.md_tx_agent_0.test_agt_tx_mbx = md_tx_test_agt_instruccion_tx;
        e0.md_tx_test_agt_num_trans_tx = md_tx_test_agt_num_trans_tx;
        e0.md_tx_agent_0.test_agt_num_tran_tx_mbx = md_tx_test_agt_num_trans_tx;

        e0.apb_test_agt_mbx = apb_test_agt_mbx;
        e0.apb_agent_0.test_agt_apb_mbx = apb_test_agt_mbx;
        e0.apb_test_agt_num_tran_mbx = apb_test_agt_num_tran_mbx;
        e0.apb_agent_0.test_agt_num_tran_apb_mbx = apb_test_agt_num_tran_mbx;

        fork
            e0.run();
        join_any

    // Prueba 1: Configuración APB
    apb_tipo_instr = APB_CONFIGURACION_INICIAL;
    apb_cant_instr = APB_UNA;
    apb_test_agt_mbx.put(apb_tipo_instr);
    apb_test_agt_num_tran_mbx.put(apb_cant_instr);
    $display("T=%0t [Test] Prueba 1: Configurando Aligner vía APB", $time);
    
    repeat(20) @(posedge md_rx_vif.clk); // Esperar que se complete la configuración
    
    // Prueba 1: Configuración TX
    md_tx_tipo_instr = TX_SIEMPRE_LISTO;
    md_tx_cant_instr = TX_UNA;
    md_tx_test_agt_instruccion_tx.put(md_tx_tipo_instr);
    md_tx_test_agt_num_trans_tx.put(md_tx_cant_instr);
    $display("T=%0t [Test] Prueba 1: Configurando MD_TX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 1: Configuración RX
    md_rx_tipo_instr = instr_validas;
    md_rx_cant_instr = cincuenta;
    md_rx_test_agt_mbx.put(md_rx_tipo_instr);
    md_rx_test_agt_num_tran_mbx.put(md_rx_cant_instr);
    $display("T=%0t [Test] Prueba 1: Configurando MD_RX", $time);

    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 2: Configuración APB
    apb_tipo_instr = APB_CONFIG_VALIDA;
    apb_cant_instr = APB_CINCO;
    apb_test_agt_mbx.put(apb_tipo_instr);
    apb_test_agt_num_tran_mbx.put(apb_cant_instr);
    $display("T=%0t [Test] Prueba 2: Configurando Aligner vía APB", $time);
    
    repeat(20) @(posedge md_rx_vif.clk); // Esperar que se complete la configuración
    
    // Prueba 2: Configuración TX
    md_tx_tipo_instr = TX_SIEMPRE_LISTO;
    md_tx_cant_instr = TX_UNA;
    md_tx_test_agt_instruccion_tx.put(md_tx_tipo_instr);
    md_tx_test_agt_num_trans_tx.put(md_tx_cant_instr);
    $display("T=%0t [Test] Prueba 2: Configurando MD_TX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 2: Configuración RX
    md_rx_tipo_instr = instr_validas;
    md_rx_cant_instr = cincuenta;
    md_rx_test_agt_mbx.put(md_rx_tipo_instr);
    md_rx_test_agt_num_tran_mbx.put(md_rx_cant_instr);
    $display("T=%0t [Test] Prueba 2: Configurando MD_RX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 3: Configuración APB
    apb_tipo_instr = APB_CONFIG_VALIDA;
    apb_cant_instr = APB_CINCO;
    apb_test_agt_mbx.put(apb_tipo_instr);
    apb_test_agt_num_tran_mbx.put(apb_cant_instr);
    $display("T=%0t [Test] Prueba 3: Configurando Aligner vía APB", $time);
    
    repeat(20) @(posedge md_rx_vif.clk); // Esperar que se complete la configuración
    
    // Prueba 3: Configuración TX
    md_tx_tipo_instr = TX_SIEMPRE_LISTO;
    md_tx_cant_instr = TX_UNA;
    md_tx_test_agt_instruccion_tx.put(md_tx_tipo_instr);
    md_tx_test_agt_num_trans_tx.put(md_tx_cant_instr);
    $display("T=%0t [Test] Prueba 3: Configurando MD_TX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 3: Configuración RX
    md_rx_tipo_instr = instr_invalidas;
    md_rx_cant_instr = quince;
    md_rx_test_agt_mbx.put(md_rx_tipo_instr);
    md_rx_test_agt_num_tran_mbx.put(md_rx_cant_instr);
    $display("T=%0t [Test] Prueba 3: Configurando MD_RX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 4: Configuración APB
    apb_tipo_instr = APB_CONFIG_VALIDA;
    apb_cant_instr = APB_CINCO;
    apb_test_agt_mbx.put(apb_tipo_instr);
    apb_test_agt_num_tran_mbx.put(apb_cant_instr);
    $display("T=%0t [Test] Prueba 4: Configurando Aligner vía APB", $time);
    
    repeat(20) @(posedge md_rx_vif.clk); // Esperar que se complete la configuración
    
    // Prueba 4: Configuración TX
    md_tx_tipo_instr = TX_BACKPRESSURE;
    md_tx_cant_instr = TX_CINCO;
    md_tx_test_agt_instruccion_tx.put(md_tx_tipo_instr);
    md_tx_test_agt_num_trans_tx.put(md_tx_cant_instr);
    $display("T=%0t [Test] Prueba 4: Configurando MD_TX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 4: Configuración RX
    md_rx_tipo_instr = instr_validas;
    md_rx_cant_instr = cincuenta;
    md_rx_test_agt_mbx.put(md_rx_tipo_instr);
    md_rx_test_agt_num_tran_mbx.put(md_rx_cant_instr);
    $display("T=%0t [Test] Prueba 4: Configurando MD_RX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 5: Configuración APB
    apb_tipo_instr = APB_CONFIG_VALIDA;
    apb_cant_instr = APB_CINCO;
    apb_test_agt_mbx.put(apb_tipo_instr);
    apb_test_agt_num_tran_mbx.put(apb_cant_instr);
    $display("T=%0t [Test] Prueba 5: Configurando Aligner vía APB", $time);
    
    repeat(20) @(posedge md_rx_vif.clk); // Esperar que se complete la configuración
    
    // Prueba 5: Configuración TX
    md_tx_tipo_instr = TX_SIEMPRE_LISTO;
    md_tx_cant_instr = TX_UNA;
    md_tx_test_agt_instruccion_tx.put(md_tx_tipo_instr);
    md_tx_test_agt_num_trans_tx.put(md_tx_cant_instr);
    $display("T=%0t [Test] Prueba 5: Configurando MD_TX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 5: Configuración RX
    md_rx_tipo_instr = llenado_aleatorio;
    md_rx_cant_instr = cincuenta;
    md_rx_test_agt_mbx.put(md_rx_tipo_instr);
    md_rx_test_agt_num_tran_mbx.put(md_rx_cant_instr);
    $display("T=%0t [Test] Prueba 5: Configurando MD_RX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 6: Configuración APB
    apb_tipo_instr = APB_ESCRIBIR_IRQ;
    apb_cant_instr = APB_CINCO;
    apb_test_agt_mbx.put(apb_tipo_instr);
    apb_test_agt_num_tran_mbx.put(apb_cant_instr);
    $display("T=%0t [Test] Prueba 5: Configurando Aligner vía APB", $time);

    repeat(20) @(posedge md_rx_vif.clk); // Esperar que se complete la configuración
    
    repeat(5000) @(posedge md_rx_vif.clk);
    $display("T=%0t [Test] Se alcanza el tiempo límite de la prueba", $time);

    // Finalizar scoreboard para generar reportes
    e0.scoreboard_0.finalize();
    
    $finish;
  endtask
endclass
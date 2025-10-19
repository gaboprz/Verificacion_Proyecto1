//================================================================================
// Módulo en el que se define el test
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

  // Definición de las condiciones iniciales del test
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

        // ASIGNAR INTERFACES PRIMERO
        e0.md_rx_vif = md_rx_vif;
        e0.md_tx_vif = md_tx_vif;
        e0.apb_vif = apb_vif;

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

    // Prueba 0: Configuración inicial APB
    apb_tipo_instr = APB_CONFIGURACION_INICIAL;
    apb_cant_instr = APB_UNA;
    apb_test_agt_mbx.put(apb_tipo_instr);
    apb_test_agt_num_tran_mbx.put(apb_cant_instr);
    $display("T=%0t [Test] Configurando Aligner vía APB", $time);
    
    repeat(20) @(posedge md_rx_vif.clk); // Esperar que se complete la configuración
    
    // AHORA configurar TX para que acepte datos
    md_tx_tipo_instr = TX_SIEMPRE_LISTO;
    md_tx_cant_instr = TX_UNA;
    md_tx_test_agt_instruccion_tx.put(md_tx_tipo_instr);
    md_tx_test_agt_num_trans_tx.put(md_tx_cant_instr);
    $display("T=%0t [Test] Configurando MD_TX", $time);
    
    repeat(100) @(posedge md_rx_vif.clk);

    // Prueba 1 para MD_RX
    md_rx_tipo_instr = instr_validas;
    md_rx_cant_instr = diez;
    md_rx_test_agt_mbx.put(md_rx_tipo_instr);
    md_rx_test_agt_num_tran_mbx.put(md_rx_cant_instr);
    $display("T=%0t [Test] Enviada la primera prueba. En el MD_RX es de tipo instrucciones validas y se envían 1 objetos", $time);
    
    repeat(1000) @(posedge md_rx_vif.clk);
    $display("T=%0t [Test] Se alcanza el tiempo límite de la prueba", $time);

    // Finalizar scoreboard para generar reportes
    e0.scoreboard_0.finalize();
    
    $finish;
  endtask
endclass
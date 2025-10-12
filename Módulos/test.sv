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

  // Definición del ambiente de prueba
  env e0;

  // Definición de interfaces
  virtual md_rx_interface md_rx_vif;



  // Definición de las condiciones iniciales del test
  function new;
    // Instanciación de mailboxes de MB_RX
    md_rx_test_agt_mbx          = new();
    md_rx_test_agt_num_tran_mbx = new();

    e0                              = new;
    e0.md_rx_vif                    = md_rx_vif;
    e0.md_rx_test_agt_mbx           = md_rx_test_agt_mbx;
    e0.md_rx_agent_0.test_agt_mbx   = md_rx_test_agt_mbx;
    e0.md_rx_test_agt_num_tran_mbx  = md_rx_test_agt_num_tran_mbx;
    e0.md_rx_agent_0.md_rx_test_agt_num_tran_mbx = md_rx_test_agt_num_tran_mbx;
    $display("T=%0t [Test] Test creado", $time);
  endfunction
  
  task run;
    $display("T=%0t [Test] Test inicializado", $time);

    fork
        e0.run();
    join_any

    // Prueba 1 para MD_RX
    md_rx_tipo_instr = llenado_aleatorio;
    md_rx_cant_instr = diez;
    md_rx_test_agt_mbx.put(llenado_aleatorio);
    md_rx_test_agt_num_tran_mbx.put(diez);
    $display("T=%0t [Test] Enviada la primera prueba. En el MD_RX es de tipo aleatorio...
    y se envían 10 objetos", $time);

    // Prueba 2 para MD_RX
    md_rx_tipo_instr = instr_validas;
    md_rx_cant_instr = cincuenta;
    md_rx_test_agt_mbx.put(instr_validas);
    md_rx_test_agt_num_tran_mbx.put(cincuenta);
    $display("T=%0t [Test] Enviada la primera prueba. En el MD_RX es con instr validas...
    y se envían 50 objetos", $time);
    
    #2000
    $display("T=%0t [Test] Se alcanza el tiempo límite de la prueba", $time);

    // Finalizar scoreboard para generar reportes
    e0.scoreboard_0.finalize();
    
    $finish;
  endtask
endclass
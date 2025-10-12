//================================================================================
// Módulo en el que se define el ambiente
//================================================================================

// Se incluyen archivos con transactores que debe contener el ambiente
`include "md_rx_agent.sv"
`include "md_tx_agent.sv"
`include "apb_agent.sv"
`include "checker.sv"
`include "scoreboard.sv"

class env;
    // Transactores del MD_RX
    md_rx_agent     md_rx_agent_0;
    md_rx_driver    md_rx_driver_0;
    md_rx_monitor   md_rx_monitor_0;

    // Transactores del MD_TX
    md_tx_driver    md_tx_driver_0;
    md_tx_monitor   md_tx_monitor_0;

    // Transactores del APB
    apb_agent       apb_agent_0;

    // Transactor del Checker
    aligner_checker aligner_checker_0;

    // Transactor del Scoreboard
    scoreboard scoreboard_0;

    // Mailboxes del MD_RX
    trans_rx_in_mbx     md_rx_gen_drv_mbx;
    trans_rx_out_mbx    md_rx_mon_scb_rx_mbx;

    comando_test_agente_MD_RX_mbx       md_rx_test_agt_mbx;
    num_trans_test_agente_MD_RX_mbx     md_rx_test_agt_num_tran_mbx;

    // Mailboxes del MD_TX

    // Mailboxes del APB

    // Mailboxes del Checker
    trans_apb_in_mbx   apb_config_chk_mbx;
    trans_rx_in_mbx    md_rx_in_chk_mbx;
    trans_rx_out_mbx   md_rx_out_chk_mbx;
    trans_tx_out_mbx   md_tx_out_chk_mbx;
    checker_result_mbx chk_scb_mbx;


    // Eventos del MD_RX
    event md_rx_drv_rx_done;

    // Eventos del MD_TX

    // Eventos del APB

    // Interfaces del MD_RX
    virtual md_rx_interface md_rx_vif;

    // Interfaces del MD_TX

    // Interfaces del APB

    function new();
        // Instanciación de transactores
        md_rx_agent_0   = new;
        md_rx_driver_0  = new;
        md_rx_monitor_0 = new;

        md_tx_driver_0  = new;
        md_tx_monitor_0 = new;

        apb_agent_0 = new;

        aligner_checker_0 = new;

        scoreboard_0 = new;

        // Instanciación de mailboxes
        md_rx_gen_drv_mbx           = new();
        md_rx_mon_scb_rx_mbx        = new();
        md_rx_test_agt_mbx          = new();
        md_rx_test_agt_num_tran_mbx = new();

        apb_config_chk_mbx  = new();
        md_rx_in_chk_mbx    = new();
        md_rx_out_chk_mbx   = new();
        md_tx_out_chk_mbx   = new();
        chk_scb_mbx         = new();


        // Conexiones de los mailboxes entre distintos transactores

        // MD_RX
        md_rx_agent_0.gen_drv_mbx   = md_rx_gen_drv_mbx;
        md_rx_driver_0.gen_drv_mbx  = md_rx_gen_drv_mbx;

        md_rx_monitor_0.mon_scb_rx_mbx = md_rx_mon_scb_rx_mbx;
        // Conexión del monitor MD_RX al scoreboard

        md_rx_agent_0.test_agt_mbx = md_rx_test_agt_mbx;

        md_rx_agent_0.test_agt_num_tran_mbx = md_rx_test_agt_num_tran_mbx;
        // La conexión con el test se realiza desde el test


        // MD_TX


        // APB

        // Transactores varios al checker

        // Se envían datos del APB, del agente al checker
        apb_agent_0.gen_chk_apb_mbx      = apb_config_chk_mbx;
        aligner_checker_0.apb_config_mbx = apb_config_chk_mbx;
        // Se envían datos del MD_RX_IN, del agente al checker
        md_rx_agent_0.gen_chk_mbx   = md_rx_in_chk_mbx; 
        aligner_checker_0.rx_in_mbx = md_rx_in_chk_mbx;
        // Se envían datos del MD_RX_OUT, del monitor al checker
        md_rx_monitor_0.mon_chk_rx_mbx = md_rx_out_chk_mbx;
        aligner_checker_0.rx_out_mbx   = md_rx_out_chk_mbx;
        // Se envían datos del MD_TX_OUT, del monitor al checker
        md_tx_monitor_0.mon_chk_tx_mbx = md_tx_out_chk_mbx;
        aligner_checker_0.tx_out_mbx   = md_tx_out_chk_mbx;
        // Se envían datos del checker al scoreboard
        aligner_checker_0.chk_scb_mbx = chk_scb_mbx;
        scoreboard_0.chk_scb_mbx      = chk_scb_mbx;


        // Conexiones de los eventos entre distintos transactores

        // MD_RX
        md_rx_driver_0.drv_rx_done = md_rx_drv_rx_done;
        md_rx_agent_0.drv_rx_done  = md_rx_drv_rx_done;

        // MD_TX


        // APB

    endfunction

    virtual task run();
        $display("T=%0t [Environment] Iniciando ambiente...", $time);

        md_rx_driver_0.vif  = md_rx_vif;
        md_rx_monitor_0.vif = md_rx_vif;

        fork
            // MB_RX
            md_rx_agent_0.run();
            md_rx_driver_0.run();
            md_rx_monitor_0.run();
            // MB_TX
            md_tx_driver_0.run();
            md_tx_monitor_0.run();
            //APB

            // Checker
            aligner_checker_0.run();
            //Scoreboard
            scoreboard_0.run();
        join_any
    endtask
endclass
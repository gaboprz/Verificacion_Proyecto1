//================================================================================
// Módulo en el que se define el ambiente
//================================================================================

// Se incluyen archivos con transactores que debe contener el ambiente
`include "transactions.sv"

`include "md_rx_agent.sv"
`include "md_tx_agent.sv"
`include "apb_agent.sv"
`include "checker.sv"
`include "scoreboard.sv"

class env;

    //--------------------------------------------------
    // TRANSACTORES
    //--------------------------------------------------
    // Transactores del MD_RX
    md_rx_agent     md_rx_agent_0;
    md_rx_driver    md_rx_driver_0;
    md_rx_monitor   md_rx_monitor_0;

    // Transactores del MD_TX
    md_tx_driver    md_tx_driver_0;
    md_tx_monitor   md_tx_monitor_0;
    md_tx_agent     md_tx_agent_0;


    // Transactores del APB
    apb_agent       apb_agent_0;
    apb_driver      apb_driver_0;
    apb_monitor     apb_monitor_0;

    // Transactor del Checker
    aligner_checker aligner_checker_0;

    // Transactor del Scoreboard
    scoreboard scoreboard_0;
    //--------------------------------------------------
    // MAILBOXES
    //--------------------------------------------------
    // Mailboxes del MD_RX
    trans_rx_in_mbx     md_rx_gen_drv_mbx; 

    comando_test_agente_MD_RX_mbx       md_rx_test_agt_mbx;
    num_trans_test_agente_MD_RX_mbx     md_rx_test_agt_num_tran_mbx;




    // Mailboxes del MD_TX
    trans_tx_in_mbx                 md_tx_gen_drv_mbx;
    comando_test_agente_MD_TX_mbx   md_tx_test_agt_instruccion_tx;
    num_trans_test_agente_MD_TX_mbx md_tx_test_agt_num_trans_tx;


    // Mailboxes del APB

    trans_apb_in_mbx                apb_gen_drv_mbx;
    comando_test_agente_APB_mbx      apb_test_agt_mbx;
    num_trans_test_agente_APB_mbx    apb_test_agt_num_tran_mbx;




    // Mailboxes del Checker
    
    trans_rx_in_mbx    md_rx_in_chk_mbx;
    trans_rx_out_mbx   md_rx_out_chk_mbx;
    trans_tx_out_mbx   md_tx_out_chk_mbx;  
    checker_result_mbx chk_scb_mbx;
    trans_apb_in_mbx   apb_config_chk_mbx;
    //--------------------------------------------------
    // EVENTOS
    //--------------------------------------------------
    // Eventos del MD_RX
    event       md_rx_drv_rx_done;
    // Eventos del MD_TX
    event       md_tx_drv_done;
    // Eventos del APB
    event       apb_drv_done;
    //--------------------------------------------------
    // INTERFACES VIRTUALES
    //--------------------------------------------------
    // Interfaces del MD_RX
    virtual md_rx_interface md_rx_vif;

    // Interfaces del MD_TX
    virtual md_tx_interface md_tx_vif;
    // Interfaces del APB
    virtual apb_interface apb_vif;
    //--------------------------------------------------
    // CONSTRUCTOR
    //--------------------------------------------------
    function new();
        // Instanciación de transactores
        md_rx_agent_0   = new;
        md_rx_driver_0  = new;
        md_rx_monitor_0 = new;
        // TX!!!md_tx_driver_0
        md_tx_driver_0  = new;
        md_tx_monitor_0 = new;
        md_tx_agent_0   = new;
        //APB!!
        apb_agent_0 = new;
        apb_driver_0 = new;
        apb_monitor_0 = new;


        aligner_checker_0 = new;

        scoreboard_0 = new;

        // Conexión de vif
        md_rx_driver_0.vif  = md_rx_vif;
        md_rx_monitor_0.vif = md_rx_vif;

        md_tx_driver_0.vif = md_tx_vif;
        md_tx_monitor_0.vif = md_tx_vif;

        apb_driver_0.vif = apb_vif;
        apb_monitor_0.vif = apb_vif;

        // VERIFICAR conexiones
        if (md_rx_driver_0.vif == null) $display("ERROR: md_rx_driver_0.vif es null");
        if (md_tx_driver_0.vif == null) $display("ERROR: md_tx_driver_0.vif es null");
        if (apb_driver_0.vif == null) $display("ERROR: apb_driver_0.vif es null");

        // Instanciación de mailboxes
        md_rx_gen_drv_mbx           = new();
        md_rx_test_agt_mbx          = new();
        md_rx_test_agt_num_tran_mbx = new();

        apb_config_chk_mbx  = new();
        md_rx_in_chk_mbx    = new();
        md_rx_out_chk_mbx   = new();
        md_tx_out_chk_mbx   = new();
        chk_scb_mbx         = new();

        //TX mbx
        md_tx_gen_drv_mbx               = new();
        md_tx_test_agt_instruccion_tx   = new();
        md_tx_test_agt_num_trans_tx     = new();

        // Mailboxes del APB

        apb_gen_drv_mbx     = new();
        apb_test_agt_mbx    = new();
        apb_test_agt_num_tran_mbx = new();

        //--------------------------------------------------
        // CONEXIONES DE MAILBOXES - MD_RX
        //--------------------------------------------------
        // MD_RX
        md_rx_agent_0.gen_drv_mbx   = md_rx_gen_drv_mbx;
        md_rx_driver_0.gen_drv_mbx  = md_rx_gen_drv_mbx;


        // Conexión del monitor MD_RX al scoreboard

        md_rx_agent_0.test_agt_mbx = md_rx_test_agt_mbx;
        md_rx_agent_0.test_agt_num_tran_mbx = md_rx_test_agt_num_tran_mbx;
        // La conexión con el test se realiza desde el test
        //--------------------------------------------------
        // CONEXIONES DE MAILBOXES - MD_TX
        //--------------------------------------------------
        //agente
        md_tx_agent_0.gen_drv_tx_mbx               = md_tx_gen_drv_mbx; 
        md_tx_agent_0.test_agt_tx_mbx               = md_tx_test_agt_instruccion_tx;
        md_tx_agent_0.test_agt_num_tran_tx_mbx      = md_tx_test_agt_num_trans_tx;
        // driver
        md_tx_driver_0.gen_drv_tx_mbx               = md_tx_gen_drv_mbx;
        //--------------------------------------------------
        // CONEXIONES DE MAILBOXES - APB
        //--------------------------------------------------
        apb_agent_0.gen_drv_apb_mbx             =apb_gen_drv_mbx;
        apb_agent_0.test_agt_apb_mbx            =apb_test_agt_mbx;
        apb_agent_0.test_agt_num_tran_apb_mbx   =apb_test_agt_num_tran_mbx;
        apb_driver_0.gen_drv_apb_mbx            = apb_gen_drv_mbx;
          
        //--------------------------------------------------
        // CONEXIONES DE MAILBOXES - CHECKER
        //--------------------------------------------------
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

        //--------------------------------------------------
        // CONEXIONES DE EVENTOS
        //--------------------------------------------------
        // Conexiones de los eventos entre distintos transactores

        // MD_RX
        md_rx_driver_0.drv_rx_done = md_rx_drv_rx_done;
        md_rx_agent_0.drv_rx_done  = md_rx_drv_rx_done;

        // MD_TX
        md_tx_driver_0.drv_tx_done  = md_tx_drv_done;
        md_tx_agent_0.drv_tx_done   = md_tx_drv_done;

        // APB
        apb_agent_0.drv_apb_done    = apb_drv_done;
        apb_driver_0.drv_apb_done   = apb_drv_done;
        

    endfunction

    virtual task run();
        $display("T=%0t [Environment] Iniciando ambiente...", $time);

        


        fork
            // MB_RX
            md_rx_agent_0.run();
            md_rx_driver_0.run();
            md_rx_monitor_0.run();
            // MB_TX
            md_tx_driver_0.run();
            md_tx_monitor_0.run();
            md_tx_agent_0.run();
            //APB
            apb_agent_0.run();
            apb_driver_0.run();
            apb_monitor_0.run();
            // Checker
            aligner_checker_0.run();
            //Scoreboard
            scoreboard_0.run();
        join_any
    endtask
endclass
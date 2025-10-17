//================================================================================
// Módulo en el que se define la interfaz para interactuar con la FIFO RX, además
// de que se define el generador, el driver y el monitor para la interacción con
// esta interfaz
//================================================================================


//================================================================================
// Definición de tipo de instrucción a generar en el agente
//================================================================================

typedef enum {llenado_aleatorio, instr_validas, instr_invalidas} instr_agente_MD_RX;


//================================================================================
// Definición de número de objetos a generar en el agente
//================================================================================

typedef enum {cinco, diez, quince, treinta, cincuenta} cantidad_inst_agente_MD_RX;


//================================================================================
// Definición de mailboxes de tipo específico
//================================================================================

typedef mailbox #(trans_rx_in)  trans_rx_in_mbx;
typedef mailbox #(trans_rx_out) trans_rx_out_mbx;

typedef mailbox #(instr_agente_MD_RX) comando_test_agente_MD_RX_mbx;
typedef mailbox #(cantidad_inst_agente_MD_RX) num_trans_test_agente_MD_RX_mbx;


//================================================================================
// Interfaz para interactuar con el DUT
//================================================================================

interface md_rx_interface (input logic clk, input logic reset_n);
    //--------------------------------------------------
    // SEÑALES (DRIVER) / Entran al DUT
    //--------------------------------------------------
    bit          md_rx_valid;  // Empezar la transaccion
    logic [31:0] md_rx_data;   // Dato de entrada
    logic [1:0]  md_rx_offset; // Offset del dato de entrada
    logic [2:0]  md_rx_size;   // Size del dato de entrada
    
    //--------------------------------------------------
    // SEÑALES (MONITOR) / Salen del DUT
    //--------------------------------------------------
    bit md_rx_ready;  // Indica que se aceptan los datos de entrada
    bit md_rx_err;    // Indica que hubo un error con los datos de entrada
    
    // --------------------------------------------------
    // MODPORTS
    // --------------------------------------------------
    
    // Para el DRIVER
    modport DRIVER (
        output md_rx_valid,  
        output md_rx_data,    
        output md_rx_offset,
        output md_rx_size,
        input  clk,          
        input  reset_n,      
        input  md_rx_ready
    );
    
    // Para el MONITOR 
    modport MONITOR (
        input md_rx_ready, 
        input md_rx_err  
    );

    // --------------------------------------------------
    // ASSERTIONS
    // --------------------------------------------------

    // Tamaños válidos
    property valid_sizes; 
        @(posedge clk) disable iff (!reset_n)
        md_rx_valid |-> (md_rx_size inside {1, 2, 4});  // ← Cambiado a RX
    endproperty
    ASSERT_VALID_SIZES: assert property (valid_sizes);
    
    // Offsets válidos 
    property valid_offsets;
        @(posedge clk) disable iff (!reset_n)
        md_rx_valid |-> (md_rx_offset inside {[0:3]});
    endproperty
    ASSERT_VALID_OFFSETS: assert property (valid_offsets);
   
endinterface

class md_rx_agent;
    trans_rx_in_mbx gen_drv_mbx;
    trans_rx_in_mbx gen_chk_mbx;
    comando_test_agente_MD_RX_mbx test_agt_mbx;
    num_trans_test_agente_MD_RX_mbx test_agt_num_tran_mbx;
    instr_agente_MD_RX instruccion;
    cantidad_inst_agente_MD_RX num_trans;
    event drv_rx_done;

    function int obtener_num_trans();
        case(num_trans)
            cinco: return 5;
            diez: return 10;
            quince: return 15;
            treinta: return 30;
            cincuenta: return 50;
            default: return 0;
        endcase
    endfunction

    task run();
        forever begin
            $display ("T=%0t [Agent MD_RX] Waiting to receive test instructions", $time);
            test_agt_mbx.get(instruccion);
            test_agt_num_tran_mbx.get(num_trans);
            $display ("T=%0t [Agent MD_RX] Received test instructions", $time);

            case(instruccion)
                // Tengo transacciones aleatorias
                llenado_aleatorio: begin
                    for (int i=0; i<obtener_num_trans(); i++) begin
                        trans_rx_in item = new();
                        // Desactivar los constraints
                        item.valid_size.constraint_mode(0);
                        item.valid_offset.constraint_mode(0);
                        item.size_offset_relation.constraint_mode(0);
                        item.invalid_size_offset_combination.constraint_mode(0);
                        item.randomize();
                        gen_drv_mbx.put(item);
                        gen_chk_mbx.put(item);
                        item.print("[Agent MB_RX] Item sent from agent to driver");

                        @(drv_rx_done);
                    end
                end
                // Activa el constraint para tener solo transacciones válidas
                instr_validas: begin
                    for (int i=0; i<obtener_num_trans(); i++) begin
                        trans_rx_in item = new();
                        item.valid_size.constraint_mode(1);
                        item.valid_offset.constraint_mode(1);
                        item.size_offset_relation.constraint_mode(1);
                        item.invalid_size_offset_combination.constraint_mode(0);
                        item.randomize();
                        gen_drv_mbx.put(item);
                        gen_chk_mbx.put(item);
                        item.print("[Agent MD_RX] Item sent from agent to driver");

                        @(drv_rx_done);
                    end
                end
                // Activa el constraint para tener solo transacciones inválidas
                instr_invalidas: begin 
                    for (int i=0; i<obtener_num_trans(); i++) begin
                        trans_rx_in item = new();
                        item.valid_size.constraint_mode(0);
                        item.valid_offset.constraint_mode(0);
                        item.size_offset_relation.constraint_mode(0);
                        item.invalid_size_offset_combination.constraint_mode(1);
                        item.randomize();
                        gen_drv_mbx.put(item);
                        gen_chk_mbx.put(item);
                        item.print("[Agent MD_RX] Item sent from agent to driver");

                        @(drv_rx_done);
                    end
                end
                // Solo envía una transacción que es válida
                default: begin
                    trans_rx_in item = new();
                        item.valid_size.constraint_mode(1);
                        item.valid_offset.constraint_mode(1);
                        item.size_offset_relation.constraint_mode(1);
                        item.invalid_size_offset_combination.constraint_mode(0);
                        item.randomize();
                        gen_drv_mbx.put(item);
                        gen_chk_mbx.put(item);
                        item.print("[Agent MD_RX] Item sent from agent to driver");

                        @(drv_rx_done);
                end
            endcase
            $display ("T=%0t [Agent MD_RX] Generation done", $time);
        end
    endtask
endclass

class  md_rx_driver;
    virtual         md_rx_interface.DRIVER vif; //CONEXIÓN DIRECTA A LA INTERFACE
    trans_rx_in_mbx gen_drv_mbx;
    event           drv_rx_done;
    task run();
        $display("T=%0t [Driver MD_RX] Iniciado", $time);

        // Inicializar señales
        vif.md_rx_valid     <= 0;
        vif.md_rx_data      <= 0;
        vif.md_rx_offset    <= 0;
        vif.md_rx_size      <= 0;

        @ (posedge vif.clk);

        forever begin
            trans_rx_in item_gen_drv_rx = new();
            
            // Obtener datos del generador
            $display ("T=%0t [Driver MD_RX] waiting for item ...", $time);
            gen_drv_mbx.get(item_gen_drv_rx);
            item_gen_drv_rx.print("[Driver MD_RX] Item received");
            // Asignacion de datos que ingresan al dut
            vif.md_rx_valid     <= 1'b1;
            vif.md_rx_data      <= item_gen_drv_rx.md_rx_data;
            vif.md_rx_offset    <= item_gen_drv_rx.md_rx_offset;
            vif.md_rx_size      <= item_gen_drv_rx.md_rx_size;

            // Esperar a que el DUT acepte la transferencia (md_rx_ready = 1)
            do begin
                @(posedge vif.clk);
            end while (!vif.md_rx_ready);

            // Una vez aceptada, se termina la transferencia
            vif.md_rx_valid <= 1'b0;
            
            // Se dispara para que el agente genere un nuevo item
            ->drv_rx_done; 
        end
    endtask

endclass

class md_rx_monitor;
    // Conexión a la interface
    virtual             md_rx_interface.MONITOR vif;
    trans_rx_out_mbx    mon_chk_rx_mbx;

    task run();
        $display("T=%0t [Monitor MD_RX] Iniciado", $time);
        
        forever begin
            trans_rx_out item_mon_scb_rx;
            // Esperar transferencia válida del DUT
            // Según documentación del Aligner:
            // A transfer ends when VALID is 1 and READY is 1
            @(posedge vif.clk);
            while (!(vif.md_rx_valid && vif.md_rx_ready)) begin
                @(posedge vif.clk);
            end
            
            // Capturar transacción
            item_mon_scb_rx               = new();
            item_mon_scb_rx.md_rx_ready   = vif.md_rx_ready;
            item_mon_scb_rx.md_rx_err     = vif.md_rx_err;
            
            // Enviar al scoreboard
            mon_chk_rx_mbx.put(item_mon_scb_rx);
            item_mon_scb_rx.print("[Monitor MD_RX] Item sent");
        end
    endtask
endclass
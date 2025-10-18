
// =================================================================================
// Definición de tipos de instrucción para el agente TX
// =================================================================================

typedef enum {
    TX_SIEMPRE_LISTO,      // Siempre ready para recibir datos
    TX_BACKPRESSURE,       // Simula ready aleatorio
    TX_INYECTAR_ERRORES   // Inyecta errores en transferencias
} instr_agente_MD_TX;

// =================================================================================
// Definición de número de transacciones para el agente TX
// =================================================================================

typedef enum {
    TX_UNA,
    TX_CINCO,
    TX_DIEZ, 
    TX_QUINCE,
    TX_TREINTA,
    TX_CINCUENTA
} cantidad_inst_agente_MD_TX;

// =================================================================================
// Mailboxes específicos para TX
// =================================================================================

typedef mailbox #(trans_tx_in) trans_tx_in_mbx;
typedef mailbox #(trans_tx_out) trans_tx_out_mbx;
typedef mailbox #(instr_agente_MD_TX) comando_test_agente_MD_TX_mbx;
typedef mailbox #(cantidad_inst_agente_MD_TX) num_trans_test_agente_MD_TX_mbx;

// =================================================================================
// Agente TX - Generador de Estímulos
// =================================================================================

class md_tx_agent;
    trans_tx_in_mbx                     gen_drv_tx_mbx;           // Hacia el driver TX         
    comando_test_agente_MD_TX_mbx       test_agt_tx_mbx;          // Comandos del test
    num_trans_test_agente_MD_TX_mbx     test_agt_num_tran_tx_mbx; // Número de transacciones
    instr_agente_MD_TX                  instruccion_tx;           // Comando actual
    cantidad_inst_agente_MD_TX          num_trans_tx;             // Cantidad de transacciones
    event                               drv_tx_done;              // Sincronización
    
    
    function int obtener_num_trans_tx();
        case(num_trans_tx)
            TX_UNA:       return 1;
            TX_CINCO:     return 5;
            TX_DIEZ:      return 10;
            TX_QUINCE:    return 15;
            TX_TREINTA:   return 30;
            TX_CINCUENTA: return 50;
            default:      return 1;
        endcase
    endfunction

    task run();
        forever begin
            $display("T=%0t [Agent MD_TX] Esperando instrucciones del test", $time);
            test_agt_tx_mbx.get(instruccion_tx);
            test_agt_num_tran_tx_mbx.get(num_trans_tx);
            $display("T=%0t [Agent MD_TX] Instrucción recibida", $time);

            case(instruccion_tx)
                // =============================================================
                // MODO 1: Siempre listo para recibir
                // =============================================================
                TX_SIEMPRE_LISTO: begin
                    for (int i = 0; i < obtener_num_trans_tx(); i++) begin
                        trans_tx_in item = new();
                        // Siempre ready, sin errores
                        item.md_tx_ready = 1'b1;
                        item.md_tx_err = 1'b0;
                        
                        gen_drv_tx_mbx.put(item);
                        item.print("[Agent MD_TX] TX_SIEMPRE_LISTO");
                        @(drv_tx_done); // Esperar que el driver procese
                    end
                end

                // =============================================================
                // MODO 2: Backpressure aleatorio (simula sistema ocupado)
                // =============================================================
                TX_BACKPRESSURE: begin
                    for (int i = 0; i < obtener_num_trans_tx(); i++) begin
                        trans_tx_in item = new();
                        // 70% ready, 30% no ready 
                        assert(item.randomize() with {
                            md_tx_ready dist { 1'b1 := 70, 1'b0 := 30 };
                            md_tx_err == 0; // Sin errores en este modo
                        });
                        
                        gen_drv_tx_mbx.put(item);
                        item.print("[Agent MD_TX] TX_BACKPRESSURE");
                        @(drv_tx_done);
                    end
                end

                // =============================================================
                // MODO 3: Inyección de errores controlada
                // =============================================================
                TX_INYECTAR_ERRORES: begin
                    for (int i = 0; i < obtener_num_trans_tx(); i++) begin
                        trans_tx_in item = new();
                        // Siempre ready, pero inyecta errores ocasionalmente
                        assert(item.randomize() with {
                            md_tx_ready == 1'b1;  // Siempre listo
                            md_tx_err dist { 1'b1 := 20, 1'b0 := 80 }; // 20% de errores
                        });
                        
                        gen_drv_tx_mbx.put(item);
                        item.print("[Agent MD_TX] TX_INYECTAR_ERRORES");
                        @(drv_tx_done);
                    end
                end

                // =============================================================
                // MODO POR DEFECTO
                // =============================================================
                default: begin
                    trans_tx_in item = new();
                    item.md_tx_ready = 1'b1;
                    item.md_tx_err = 1'b0;
                    gen_drv_tx_mbx.put(item);
                    item.print("[Agent MD_TX] DEFAULT");
                    @(drv_tx_done);
                end
            endcase
            
            $display("T=%0t [Agent MD_TX] Generación completada", $time);
        end
    endtask
endclass

interface md_tx_interface (input logic clk, input logic reset_n);
    //--------------------------------------------------
    // SEÑALES (DRIVER)
    //--------------------------------------------------
    logic md_tx_ready;  // El testbench controla cuándo está listo para recibir
    logic md_tx_err;    // El testbench inyecta errores
    
    //--------------------------------------------------
    // SEÑALES (MONITOR)
    //--------------------------------------------------
    logic md_tx_valid;          // DUT indica que los datos son válidos
    logic [31:0] md_tx_data;    // Datos alineados que salen del DUT
    logic [1:0] md_tx_offset;   // Offset de los datos de salida
    logic [2:0] md_tx_size;     // Tamaño de los datos de salida
    
    // --------------------------------------------------
    // MODPORTS
    // --------------------------------------------------
    
    // Para el DRIVER - controla ready y error
    modport DRIVER (
        output md_tx_ready,  // El driver PUEDE escribir ready
        output md_tx_err,    // El driver PUEDE escribir error
        input  clk,          // El driver SOLO PUEDE leer el clk
        input  reset_n       // El driver SOLO PUEDE leer el reset
    );
    
    // Para el MONITOR - solo observa (lee)
    modport MONITOR (
        input md_tx_valid,   // El monitor SOLO LEE valid
        input md_tx_data,    // El monitor SOLO LEE data
        input md_tx_offset,  // El monitor SOLO LEE offset
        input md_tx_size,    // El monitor SOLO LEE size
        input md_tx_ready,  
        input md_tx_err,
        input clk,           // El monitor SOLO LEE clk
        input reset_n        // El monitor SOLO LEE reset
    );
    
    // Para el DUT - recibe de driver y envía a monitor
    modport DUT (
        input  clk, 
        input  reset_n,
        input  md_tx_ready,  // El DUT RECIBE ready del driver
        input  md_tx_err,    // El DUT RECIBE error del driver
        output md_tx_valid,  // El DUT ENVÍA valid al monitor
        output md_tx_data,   // El DUT ENVÍA data al monitor
        output md_tx_offset, // El DUT ENVÍA offset al monitor
        output md_tx_size    // El DUT ENVÍA size al monitor
    );

     // --------------------------------------------------
    // ASSERTIONS
    // --------------------------------------------------

    // Valid durante transferencia debe ser estable
    property stable_valid_during_transfer;
        @(posedge clk) disable iff (!reset_n)
        (md_tx_valid && !md_tx_ready) |=> md_tx_valid;
    endproperty
    ASSERT_STABLE_VALID: assert property (stable_valid_during_transfer);
    
    // Datos estables durante transferencia
    property stable_data_during_transfer;
        @(posedge clk) disable iff (!reset_n)
        (md_tx_valid && !md_tx_ready) |=> 
        $stable(md_tx_data) && $stable(md_tx_offset) && $stable(md_tx_size);
    endproperty
    ASSERT_STABLE_DATA: assert property (stable_data_during_transfer);
    
    // Tamaños válidos
    property valid_sizes; 
        @(posedge clk) disable iff (!reset_n)
        md_tx_valid |-> (md_tx_size inside {1, 2, 4});
    endproperty
    ASSERT_VALID_SIZES: assert property (valid_sizes);
    
    // Offsets válidos 
    property valid_offsets;
        @(posedge clk) disable iff (!reset_n)
        md_tx_valid |-> (md_tx_offset inside {[0:3]});
    endproperty
    ASSERT_VALID_OFFSETS: assert property (valid_offsets);
endinterface

class  md_tx_driver;
    virtual md_tx_interface.DRIVER vif; //CONEXIÓN DIRECTA A LA INTERFACE
    trans_tx_in_mbx gen_drv_tx_mbx;
    event drv_tx_done;


    task run();
        $display("T=%0t [Driver MD_TX] driver iniciado", $time);

        // Inicializar señales
        vif.md_tx_ready <= 0;
        vif.md_tx_err <= 0;

        //Esperar reset 
        wait(vif.reset_n == 1);

        forever begin
            trans_tx_in item_dv_tx = new();
            
            //obtener datos del generador
            gen_drv_tx_mbx.get(item_dv_tx);
            item_dv_tx.print("TX Driver");
            //Asignacion de datos que ingresan al dut
            vif.md_tx_ready <= item_dv_tx.md_tx_ready;
            vif.md_tx_err <= item_dv_tx.md_tx_err;
             $display("T=%0t [TX Driver] Configurado: ready=%0d, err=%0d", 
                     $time, item_dv_tx.md_tx_ready, item_dv_tx.md_tx_err);
            @(posedge vif.clk);
            ->drv_tx_done;
        end
    endtask

endclass

class md_tx_monitor;
    virtual md_tx_interface.MONITOR vif;
    trans_tx_out_mbx mon_chk_tx_mbx;
    string name = "TX_Monitor";

    task run();
        $display("T=%0t [Monitor MD_TX] Monitor iniciado", $time, name);
        
        wait(vif.reset_n == 1);
        $display("T=%0t [Monitor MD_TX] Sistema listo", $time, name);
        
        forever begin
            trans_tx_out item_mon_tx;

            // Esperar FINAL de transferencia 
            @(posedge vif.clk iff (vif.md_tx_valid && vif.md_tx_ready));
            
            item_mon_tx               = new();
            item_mon_tx.md_tx_valid   = vif.md_tx_valid;
            item_mon_tx.md_tx_data    = vif.md_tx_data;
            item_mon_tx.md_tx_offset  = vif.md_tx_offset;
            item_mon_tx.md_tx_size    = vif.md_tx_size;
            item_mon_tx.md_tx_ready   = vif.md_tx_ready;
            item_mon_tx.md_tx_err     = vif.md_tx_err;
            
            // Enviar al checker
            mon_chk_tx_mbx.put(item_mon_tx);
            item_mon_tx.print($sformatf("[%s] Transferencia completada", name));
        end
    endtask
endclass



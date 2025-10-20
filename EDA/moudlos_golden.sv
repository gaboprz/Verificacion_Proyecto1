class trans_apb_in;

  rand bit          psel;     
  rand bit          penable;  
  rand bit          pwrite;   
  rand logic [15:0] paddr;    
  rand logic [31:0] pwdata;   

  function void print(string tag="");
    $display("T=%0t %s psel=0x%0h, penable=0x%0h, pwrite=0x%0h, paddr=0x%0h, pwdata=0x%0h", 
             $time,tag, psel, penable, pwrite, paddr, pwdata);
  endfunction

endclass


//================================================================================
// Clase de transacción / paquete APB de salida.
//================================================================================

class trans_apb_out;

  bit          pready;   
  logic [31:0] prdata;   
  bit          pslverr; 
  logic [15:0] paddr; 
  bit          pwrite;
  bit          psel;
  bit          penable;
  logic [31:0] pwdata;

  function void print(string tag="");
    $display("T=%0t %s pready=0x%0h, prdata=0x%0h, pslverr=0x%0h", 
             $time,tag, pready, prdata, pslverr);
  endfunction

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO RX de entrada
//================================================================================
class trans_rx_in;

  rand bit          md_rx_valid;
  rand logic [31:0] md_rx_data;
  rand logic [1:0]  md_rx_offset;
  rand logic [2:0]  md_rx_size;

  // Constraints
  constraint valid_size {
      md_rx_size inside {1, 2, 4};
  }

  constraint valid_offset {
      md_rx_offset inside {0, 1, 2, 3};
  }

  constraint size_offset_relation {
      if (md_rx_size == 1) {
          md_rx_offset inside {0, 1, 2, 3};
      }
      else if (md_rx_size == 2) {
          md_rx_offset inside {0, 2};
      }
      else if (md_rx_size == 4) {
          md_rx_offset == 0;
      }
  }

  constraint invalid_size_offset_combination {
    // Forzar combinaciones inválidas
    (md_rx_size == 1 && md_rx_offset > 3) ||
    (md_rx_size == 2 && !(md_rx_offset inside {0, 2})) ||
    (md_rx_size == 4 && md_rx_offset != 0) ||
    (md_rx_size == 3) ||
    (md_rx_size > 4) ||
    (md_rx_size == 0);
  }

  function void print(string tag="");
    $display("T=%0t %s md_rx_valid=0x%0h, md_rx_data=0x%0h, md_rx_offset=0x%0h, md_rx_size=0x%0h", 
             $time,tag, md_rx_valid, md_rx_data, md_rx_offset, md_rx_size);
  endfunction

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO RX de salida
//================================================================================

class trans_rx_out;

  bit md_rx_ready;
  bit md_rx_err;

  function void print(string tag="");
    $display("T=%0t %s md_rx_ready=0x%0h, md_rx_err=0x%0h", 
             $time, tag, md_rx_ready, md_rx_err);
  endfunction

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO TX de entrada
//================================================================================


class trans_tx_in;
  rand bit md_tx_ready;
  rand bit md_tx_err;
  bit      md_tx_valid;

    function void print(string tag="");
        $display("T=%0t [%s] md_tx_ready=0x%0h, md_tx_err=0x%0h", 
                 $time, tag, md_tx_ready, md_tx_err);  
    endfunction

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO TX de salida
//================================================================================

class trans_tx_out;
  bit          md_tx_valid;
  logic [31:0] md_tx_data;
  logic [1:0]  md_tx_offset;
  logic [2:0]  md_tx_size;
  bit          md_tx_ready;  
  bit          md_tx_err;

    function void print(string tag="");
        $display("T=%0t [%s] valid=0x%0h, data=0x%0h, offset=0x%0h, size=0x%0h, ready=0x%0h, err=0x%0h", 
                 $time, tag, md_tx_valid, md_tx_data, md_tx_offset, md_tx_size, md_tx_ready, md_tx_err);
    endfunction
endclass


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
        input  reset_n,       // El driver SOLO PUEDE leer el reset
        input md_tx_valid
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

        @ (posedge vif.clk);

    
        wait(vif.reset_n == 1);

        forever begin
            // Consumir config si llega (no bloquear)
            trans_tx_in cfg;
            if (gen_drv_tx_mbx.try_get(cfg)) begin
                cfg.print("[Driver MD_TX, Config recibida]");
                vif.md_tx_err <= cfg.md_tx_err;  // o cambiar modo de backpressure si quieres
            end

            @(posedge vif.clk);

            vif.md_tx_ready <= 1'b1;
            

            // Notificar cuando realmente se aceptó un dato
            if (vif.md_tx_valid && vif.md_tx_ready) begin
                $display("T=%0t [Driver MD_TX] Se acepta dato (valid&ready=1)", $time);
                ->drv_tx_done;
            end
        end
    endtask

endclass

class md_tx_monitor;
    virtual md_tx_interface.MONITOR vif;
    trans_tx_out_mbx mon_chk_tx_mbx;
    string name = "TX_Monitor";
    
    task run();
        $display("T=%0t [Monitor MD_TX] Monitor iniciado", $time );
        
        wait(vif.reset_n == 1);
        $display("T=%0t [Monitor MD_TX] Sistema listo", $time );
        
        forever begin
            trans_tx_out item_mon_tx;

            // Esperar FINAL de transferencia 
            @(posedge vif.clk);
            while (!(vif.md_tx_valid && vif.md_tx_ready)) begin
                @(posedge vif.clk);
            end
            
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

typedef enum {una, cinco, diez, quince, treinta, cincuenta} cantidad_inst_agente_MD_RX;


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
        input md_rx_err,
        input clk, 
        input md_rx_valid
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
            una: return 1;
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

        // PROTECCIÓN CRÍTICA: Verificar que la interfaz esté conectada
        if (vif == null) begin
            $display("ERROR CRÍTICO: Interface virtual no conectada en MD_RX Driver");
            $display("Por favor verificar la conexión en env.sv y test.sv");
            $finish;
        end

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
      
      //================================================================================
// Módulo en el que se define la interfaz para interactuar con el "Register File", 
// además de que se define el agente, el driver y el monitor para la interacción 
// con esta interfaz
//================================================================================
//================================================================================
// Módulo en el que se define la interfaz para interactuar con el "Register File"
//================================================================================


interface apb_interface (input logic pclk, input logic preset_n);
    //--------------------------------------------------
    // SEÑALES APB 
    //--------------------------------------------------
    logic [15:0] paddr;
    logic        pwrite;
    logic        psel;
    logic        penable;
    logic [31:0] pwdata;
    logic        pready;
    logic [31:0] prdata;
    logic        pslverr;

    // --------------------------------------------------
    // MODPORTS
    // --------------------------------------------------
    modport DRIVER (
        output paddr, pwrite, psel, penable, pwdata,
        input  pclk, preset_n, pready
    );
    
    modport MONITOR (
        input paddr, pwrite, psel, penable, pwdata, pready, prdata, pslverr,
        input pclk, preset_n
    );
    
    modport DUT (
        input  paddr, pwrite, psel, penable, pwdata,
        output pready, prdata, pslverr,
        input  pclk, preset_n
    );

    // --------------------------------------------------
    // ASSERTIONS CORREGIDOS
    // --------------------------------------------------
    property valid_penable;
        @(posedge pclk) disable iff (!preset_n)
        penable |-> psel;
    endproperty
    APB_ASSERT_VALID_PENABLE: assert property (valid_penable); 

    property stable_signals;
        @(posedge pclk) disable iff (!preset_n)
        (psel && !penable) |=> $stable(paddr) && $stable(pwrite) && $stable(pwdata);
    endproperty
    APB_ASSERT_STABLE_SIGNALS: assert property (stable_signals); 



endinterface



typedef enum {

    // Configuración y operaciones con CTRL
    APB_CONFIGURACION_INICIAL,    // Secuencia completa de arranque
    APB_CONFIG_VALIDA,            // Múltiples configs válidas
    APB_CONFIG_INVALIDA,          //Múltiples configs inválidas

    // Gestión de interrupciones  
    APB_ESCRIBIR_IRQEN,           // Escribe IRQEN
    APB_ESCRIBIR_IRQ,             // Escribe IRQ (clear)
    
    // Lecturas de registros
    APB_LEER_STATUS,              // Lee STATUS
    APB_LEER_IRQEN,               // Lee IRQEN
    APB_LEER_IRQ,                 // Lee IRQ
    
    // Pruebas especiales
    APB_ACCESO_ILEGAL,            // Acceso a dirección inválida
    APB_SECUENCIA_PERSONALIZADA   // Secuencia: escribir→leer→verificar
    
} instr_agente_APB;

// =================================================================================
// Definición de número de transacciones
// =================================================================================

typedef enum {
    APB_UNA,
    APB_CINCO,
    APB_DIEZ, 
    APB_QUINCE,
    APB_TREINTA,
    APB_CINCUENTA
} cantidad_inst_agente_APB;

// =================================================================================
// Mailboxes específicos para APB
// =================================================================================
typedef mailbox #(trans_apb_in) trans_apb_in_mbx;
typedef mailbox #(instr_agente_APB) comando_test_agente_APB_mbx;
typedef mailbox #(cantidad_inst_agente_APB) num_trans_test_agente_APB_mbx;
// =================================================================================
// Agente APB 
// =================================================================================

class apb_agent;
    
    // Mailboxes
    trans_apb_in_mbx                 gen_drv_apb_mbx;
    trans_apb_in_mbx                 gen_chk_apb_mbx;
    comando_test_agente_APB_mbx      test_agt_apb_mbx;
    num_trans_test_agente_APB_mbx    test_agt_num_tran_apb_mbx;
    
    // Variables de control
    instr_agente_APB                 instruccion_apb;
    cantidad_inst_agente_APB         num_trans_apb;
    event                            drv_apb_done;
    
    // Direcciones de registros
    localparam bit [15:0] CTRL_ADDR   = 16'h0000;
    localparam bit [15:0] STATUS_ADDR = 16'h000C;
    localparam bit [15:0] IRQEN_ADDR  = 16'h00F0;
    localparam bit [15:0] IRQ_ADDR    = 16'h00F4;

    // Direcciones ilegales
    localparam bit [15:0] DIRECCIONES_ILEGALES [6] = '{
        16'h0004, 16'h0008, 16'h0010, 
        16'h00F8, 16'h00FC, 16'h0100
    };

    // Pool de errores GARANTIZADOS
    bit [31:0] todos_los_errores [8] = '{
        32'h00000000, // SIZE=0
        32'h00000300, // SIZE=3
        32'h00000500, // SIZE=5
        32'h00000600, // SIZE=6
        32'h00000700, // SIZE=7
        32'h00000401, // SIZE=4, OFFSET=1
        32'h00000201, // SIZE=2, OFFSET=1
        32'h00000403  // SIZE=4, OFFSET=3
    };

    // =============================================================================
    // FUNCIONES AUXILIARES
    // =============================================================================

    function int obtener_num_trans_apb();
        case(num_trans_apb)
            APB_UNA:       return 1;
            APB_CINCO:     return 5;
            APB_DIEZ:      return 10;
            APB_QUINCE:    return 15;
            APB_TREINTA:   return 30;
            APB_CINCUENTA: return 50;
            default:       return 1;
        endcase
    endfunction

    // Función para generar configuraciones CTRL válidas ALEATORIAS
    function automatic bit [31:0] generar_config_ctrl(bit incluir_clear);
        bit [2:0] size;
        bit [1:0] offset;
        bit clear_bit;
        
        // Generar combinaciones válidas aleatorias
        size = ($urandom % 3); // 0,1,2
        case(size)
            0: size = 3'h1;  // 1 byte
            1: size = 3'h2;  // 2 bytes  
            2: size = 3'h4;  // 4 bytes
        endcase
        
        // Offset compatible con el size
        case(size)
            3'h1: offset = $urandom % 4;        // 0,1,2,3
            3'h2: offset = ($urandom % 2) * 2;  // 0,2
            3'h4: offset = 0;                   // solo 0
        endcase
        
        clear_bit = incluir_clear ? 1'b1 : 1'b0;
        
        return {15'b0, clear_bit, 6'b0, offset, 5'b0, size};
    endfunction

    task run();
        forever begin
            test_agt_apb_mbx.get(instruccion_apb);
            test_agt_num_tran_apb_mbx.get(num_trans_apb);
            

            case(instruccion_apb)
                // =============================================================
                // MODO 1: Configuración inicial (SECUENCIA COMPLETA)
                // =============================================================
                APB_CONFIGURACION_INICIAL: begin
                    trans_apb_in item_ctrl;
                    trans_apb_in item_irqen;

                    $display("T=%0t [APB AGENTE] Ejecutando secuencia de configuración inicial", $time);
                    
                    // 1. Configurar CTRL con una configuración válida
                    item_ctrl = new();
                    item_ctrl.psel = 1'b1; 
                    item_ctrl.penable = 1'b0; 
                    item_ctrl.pwrite = 1'b1;
                    item_ctrl.paddr = CTRL_ADDR;
                    item_ctrl.pwdata = generar_config_ctrl(0);
                    gen_drv_apb_mbx.put(item_ctrl); 
                    gen_chk_apb_mbx.put(item_ctrl);
                    item_ctrl.print("[APB AGENTE]  CONFIG_INICIAL - CTRL");
                    @(drv_apb_done);

                    // 2. Configurar IRQEN (habilitar todas las interrupciones)
                    item_irqen = new();
                    item_irqen.psel = 1'b1; 
                    item_irqen.penable = 1'b0; 
                    item_irqen.pwrite = 1'b1;
                    item_irqen.paddr = IRQEN_ADDR;
                    item_irqen.pwdata = 32'h0000001F;
                    gen_drv_apb_mbx.put(item_irqen); 
                    gen_chk_apb_mbx.put(item_irqen);
                    item_irqen.print(" [APB AGENTE]  CONFIG_INICIAL - IRQEN");
                    @(drv_apb_done);

                    $display("T=%0t  [APB AGENTE]  Configuración inicial completada", $time);
                end

                // =============================================================
                // MODO 2: Configuraciones válidas
                // =============================================================
                //Verificar que el Aligner acepta todas las combinaciones 
                //válidas de SIZE y OFFSET

                APB_CONFIG_VALIDA: begin
                    int num_configs = obtener_num_trans_apb();

                    trans_apb_in item = new();

                    $display("T=%0t  [APB AGENTE]  Probando %0d configuraciones válidas diferentes", $time, num_configs);
                    
                    for (int i = 0; i < num_configs; i++) begin
                        item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b1;
                        item.paddr = CTRL_ADDR;
                        item.pwdata = generar_config_ctrl(i % 2); // Alternar CLEAR
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf(" [APB AGENTE]  CONFIG_VALIDA %0d", i+1));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 3:Configuraciones invalidas
                // =============================================================
                //Verificar que el Aligner rechaza correctamente configuraciones 
                //invalidas y no se corrompe con entradas incorrectas

                APB_CONFIG_INVALIDA: begin
                    trans_apb_in item;

                    int num_errores = obtener_num_trans_apb();
                    $display("T=%0t  [APB AGENTE]  Probando %0d configuraciones inválidas", $time, num_errores);
                    
                    for (int i = 0; i < num_errores; i++) begin
                        item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b1;
                        item.paddr = CTRL_ADDR;
                        item.pwdata = todos_los_errores[i % 8];
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf(" [APB AGENTE]  Configuracion invalida %0d", i+1));
                        @(drv_apb_done);
                    end
                end 






                // =============================================================
                // MODO 4: ESCRIBIR IRQEN
                // =============================================================
                APB_ESCRIBIR_IRQEN: begin
                    trans_apb_in item;

                    int num_escrituras = obtener_num_trans_apb();
                    $display("T=%0t  [APB AGENTE]  %0d escrituras a IRQEN", $time, num_escrituras);
                    
                    for (int i = 0; i < num_escrituras; i++) begin
                        item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b1;
                        item.paddr = IRQEN_ADDR;
                        
                        // Diferentes patrones de habilitación de IRQ
                        case(i % 6)
                            0: item.pwdata = 32'h00000001; // Solo RX_FIFO_EMPTY
                            1: item.pwdata = 32'h00000003; // RX_FIFO_EMPTY + RX_FIFO_FULL
                            2: item.pwdata = 32'h00000007; // + TX_FIFO_EMPTY
                            3: item.pwdata = 32'h0000000F; // + TX_FIFO_FULL  
                            4: item.pwdata = 32'h0000001F; // Todas las IRQ
                            5: item.pwdata = 32'h00000000; // Ninguna IRQ
                        endcase
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf(" [APB AGENTE]  ESCRIBIR_IRQEN %0d/%0d", i+1, num_escrituras));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 5: ESCRIBIR IRQ (CLEAR)
                // =============================================================
                APB_ESCRIBIR_IRQ: begin
                    trans_apb_in item;

                    int num_escrituras = obtener_num_trans_apb();
                    $display("T=%0t  [APB AGENTE]  %0d escrituras a IRQ (clear)", $time, num_escrituras);
                    
                    for (int i = 0; i < num_escrituras; i++) begin
                        item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b1;
                        item.paddr = IRQ_ADDR;
                        
                        // Clear de diferentes combinaciones de IRQ
                        case(i % 5)
                            0: item.pwdata = 32'h00000001; // Clear RX_FIFO_EMPTY
                            1: item.pwdata = 32'h00000002; // Clear RX_FIFO_FULL
                            2: item.pwdata = 32'h00000004; // Clear TX_FIFO_EMPTY
                            3: item.pwdata = 32'h00000008; // Clear TX_FIFO_FULL
                            4: item.pwdata = 32'h0000001F; // Clear todas
                        endcase
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf(" [APB AGENTE]  ESCRIBIR_IRQ %0d/%0d", i+1, num_escrituras));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 6: LEER STATUS
                // =============================================================
                APB_LEER_STATUS: begin
                    trans_apb_in item;

                    int num_lecturas = obtener_num_trans_apb();
                    $display("T=%0t  [APB AGENTE]  %0d lecturas consecutivas de STATUS", $time, num_lecturas);
                    
                    for (int i = 0; i < num_lecturas; i++) begin
                        item = new();
                        item.psel = 1'b1;
                        item.penable = 1'b0;
                        item.pwrite = 1'b0;           // LECTURA
                        item.paddr = STATUS_ADDR;     
                        item.pwdata = 32'h0;          
                        
                        gen_drv_apb_mbx.put(item);
                        gen_chk_apb_mbx.put(item);
                        
                        item.print($sformatf(" [APB AGENTE]  LEER_STATUS %0d/%0d", i+1, num_lecturas));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 7: LEER IRQEN
                // =============================================================
                APB_LEER_IRQEN: begin
                    trans_apb_in item;

                    int num_lecturas = obtener_num_trans_apb();
                    $display("T=%0t  [APB AGENTE]  %0d lecturas de IRQEN", $time, num_lecturas);
                    
                    for (int i = 0; i < num_lecturas; i++) begin
                        item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b0;  // LECTURA
                        item.paddr = IRQEN_ADDR;
                        item.pwdata = 32'h0;
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf(" [APB AGENTE]  LEER_IRQEN %0d/%0d", i+1, num_lecturas));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 8: LEER IRQ
                // =============================================================
                APB_LEER_IRQ: begin
                    trans_apb_in item;
                    int num_lecturas = obtener_num_trans_apb();
                    $display("T=%0t  [APB AGENTE]  %0d lecturas de IRQ", $time, num_lecturas);
                    
                    for (int i = 0; i < num_lecturas; i++) begin
                        item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b0;  // LECTURA
                        item.paddr = IRQ_ADDR;
                        item.pwdata = 32'h0;
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf(" [APB AGENTE]  LEER_IRQ %0d/%0d", i+1, num_lecturas));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 9: ACCESO ILEGAL
                // =============================================================
                APB_ACCESO_ILEGAL: begin
                    trans_apb_in item;

                    int num_accesos = obtener_num_trans_apb();
                    $display("T=%0t  [APB AGENTE]  %0d accesos ilegales", $time, num_accesos);
                    
                    for (int i = 0; i < num_accesos; i++) begin
                        item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = $urandom_range(0, 1); // Lectura o escritura aleatoria
                        item.paddr = DIRECCIONES_ILEGALES[i % 6];
                        item.pwdata = $urandom();
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf(" [APB AGENTE]  ACCESO_ILEGAL %0d/%0d", i+1, num_accesos));
                        @(drv_apb_done);
                    end
                end



                // =============================================================
                // SECUENCIA 
                // =============================================================
                APB_SECUENCIA_PERSONALIZADA: begin
                    trans_apb_in item_escritura;
                    trans_apb_in item_lectura;
                    trans_apb_in item_status;

                    int num_secuencias = obtener_num_trans_apb();
                    $display("T=%0t  [APB AGENTE]  Ejecutando %0d secuencias personalizadas", $time, num_secuencias);
                    
                    for (int i = 0; i < num_secuencias; i++) begin
                        // SECUENCIA FIJA: Escribir CTRL → Leer CTRL → Leer STATUS
                        
                        // 1. ESCRIBIR configuración CTRL
                        item_escritura = new();
                        item_escritura.psel = 1'b1; 
                        item_escritura.penable = 1'b0; 
                        item_escritura.pwrite = 1'b1;
                        item_escritura.paddr = CTRL_ADDR;
                        item_escritura.pwdata = generar_config_ctrl(0);
                        gen_drv_apb_mbx.put(item_escritura); 
                        gen_chk_apb_mbx.put(item_escritura);
                        item_escritura.print($sformatf(" [APB AGENTE]  SECUENCIA %0d - Escritura CTRL", i));
                        @(drv_apb_done);
                        
                        // 2. LEER CTRL para verificar
                        item_lectura = new();
                        item_lectura.psel = 1'b1; 
                        item_lectura.penable = 1'b0; 
                        item_lectura.pwrite = 1'b0;
                        item_lectura.paddr = CTRL_ADDR;
                        item_lectura.pwdata = 32'h0;
                        gen_drv_apb_mbx.put(item_lectura); 
                        gen_chk_apb_mbx.put(item_lectura);
                        item_lectura.print($sformatf(" [APB AGENTE]  SECUENCIA %0d - Lectura CTRL", i));
                        @(drv_apb_done);
                        
                        // 3. LEER STATUS para ver estado general
                        item_status = new();
                        item_status.psel = 1'b1; 
                        item_status.penable = 1'b0; 
                        item_status.pwrite = 1'b0;
                        item_status.paddr = STATUS_ADDR;
                        item_status.pwdata = 32'h0;
                        gen_drv_apb_mbx.put(item_status); 
                        gen_chk_apb_mbx.put(item_status);
                        item_status.print($sformatf(" [APB AGENTE]  SECUENCIA %0d - Lectura STATUS", i));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO POR DEFECTO
                // =============================================================
                default: begin
                    trans_apb_in item;

                    $display("T=%0t  [APB AGENTE]  Modo no reconocido, usando operación por defecto", $time);
                    
                    item = new();
                    item.psel = 1'b1; 
                    item.penable = 1'b0; 
                    item.pwrite = 1'b1;
                    item.paddr = CTRL_ADDR;
                    item.pwdata = generar_config_ctrl(0); // Configuración simple por defecto
                    
                    gen_drv_apb_mbx.put(item); 
                    gen_chk_apb_mbx.put(item);
                    item.print(" [APB AGENTE]  DEFAULT");
                    @(drv_apb_done);
                end
            endcase
            
            $display("T=%0t [Agent APB] Ejecución completada", $time);
        end
    endtask
endclass

// =================================================================================
// Driver APB 
// =================================================================================

class apb_driver;
    virtual apb_interface.DRIVER vif;
    trans_apb_in_mbx            gen_drv_apb_mbx;
    event                       drv_apb_done;
    
    string name = "APB_DRIVER";
    
    task run();
        $display("T=%0t [APB Driver] Driver APB iniciado", $time );
        
        // Inicializar señales APB
        vif.psel    <= 1'b0;
        vif.penable <= 1'b0;
        vif.pwrite  <= 1'b0;
        vif.paddr   <= 16'h0;
        vif.pwdata  <= 32'h0;
        
        wait(vif.preset_n == 1);
        $display("T=%0t [APB Driver] Sistema listo", $time);
        
        forever begin
            trans_apb_in item_drv_apb = new();
            
            // Obtener transacción del agente
            gen_drv_apb_mbx.get(item_drv_apb);
            item_drv_apb.print($sformatf("[%s] Transacción recibida ", name));

            // --------------------------------------------------
            // FASE 1: SETUP PHASE 
            // --------------------------------------------------
             @(posedge vif.pclk);
            vif.psel    <= 1'b1;           // Activar psel
            vif.penable <= 1'b0;           // penable = 0 en SETUP
            vif.pwrite  <= item_drv_apb.pwrite;
            vif.paddr   <= item_drv_apb.paddr;
            vif.pwdata  <= item_drv_apb.pwdata;
            
            $display("T=%0t [APB Driver] SETUP: psel=1, penable=0 ", $time );

            // --------------------------------------------------
            // FASE 2: ACCESS PHASE 
            // --------------------------------------------------
            @(posedge vif.pclk);
            vif.penable <= 1'b1;           // penable = 1 en ACCESS
            
            $display("T=%0t [APB Driver] ACCESS: psel=1, penable=1 - DUT procesando... ", $time );
            
            // --------------------------------------------------
            @(posedge vif.pclk);
            while (vif.pready!== 1'b1) begin
                @(posedge vif.pclk);
            end

            
            // el DUT siempre responde con pready=1 en el SIGUIENTE ciclo
            // (según la lógica de código cfs_regs.v)
            $display("T=%0t [APB Driver] DUT respondió: pready=%0h ", 
                     $time , vif.pready);
            
            // --------------------------------------------------
            // FASE 3: TERMINAR TRANSACCIÓN
            // --------------------------------------------------
            vif.psel    <= 1'b0;
            vif.penable <= 1'b0;
            
            $display("T=%0t [APB Driver] Transacción finalizada", $time );
            
            -> drv_apb_done;
        end
    endtask
endclass



// =================================================================================
// Monitor APB 
// =================================================================================

class apb_monitor;
    virtual             apb_interface.MONITOR vif;      
    //trans_apb_out_mbx   mon_chk_apb_mbx;  // Envía transacciones al checker //no usado :(
    
    string name = "APB_MONITOR";
    

    task run();
        $display("T=%0t  [APB MONITOR]  Monitor APB iniciado", $time );
        
        wait(vif.preset_n == 1);
        
        forever begin
            trans_apb_out item_mon_apb;

            // Esperar una transacción APB COMPLETA
            // Según protocolo: termina cuando psel=1, penable=1, pready=1
            wait(vif.psel == 1'b1 && vif.penable == 1'b1 && vif.pready == 1'b1);
            
            item_mon_apb = new();
            
            // Información de CONTROL 
            item_mon_apb.paddr   = vif.paddr;
            item_mon_apb.pwrite  = vif.pwrite;
            item_mon_apb.psel    = vif.psel;
            item_mon_apb.penable = vif.penable;
            item_mon_apb.pwdata  = vif.pwdata;
            
            // RESPUESTA del DUT 
            item_mon_apb.pready  = vif.pready;
            item_mon_apb.prdata  = vif.prdata;
            item_mon_apb.pslverr = vif.pslverr;


            //mon_chk_apb_mbx.put(item_mon_apb);
            item_mon_apb.print($sformatf("[%s] Transacción capturada", name ));
            
            $display("T=%0t  [APB MONITOR]  Transacción enviada al checker", $time );
            
            // evitar duplicados
            @(posedge vif.pclk);
        end
    endtask
    
    
endclass







//================================================================================
// Checker para validar el funcionamiento del Aligner
//================================================================================

//================================================================================
// Clase para reportar resultados al Scoreboard
//================================================================================
class checker_result;
    // Información de la verificación
    bit         test_passed;           // ¿Pasó la prueba?
    string      test_description;      // Descripción
    string      error_message;         // Mensaje (ok/falla)
    realtime    timestamp;             // Momento

    // NUEVO: identificadores de secuencia
    int         rx_seq_id;             // N° de RX usado/checado
    int         tx_seq_id;             // N° de TX usado/checado (0 si no aplica)

    // Datos relevantes
    logic [31:0] rx_data;
    logic [1:0]  rx_offset;
    logic [2:0]  rx_size;
    logic [31:0] tx_data;
    logic [1:0]  tx_offset;
    logic [2:0]  tx_size;
    logic [2:0]  config_size;
    logic [1:0]  config_offset;

    // Contadores internos (si quieres usarlos luego)
    int checks_passed;
    int checks_failed;

    function void print(string tag="");
        $display("T=%0t %s ============================================", $time, tag);
        $display("T=%0t %s TEST: %s", $time, tag, test_description);
        $display("T=%0t %s RESULT: %s", $time, tag, test_passed ? "PASSED" : "FAILED");
        $display("T=%0t %s INFO: %s", $time, tag, error_message);
        $display("T=%0t %s SEQ: RX=%0d  TX=%0d", $time, tag, rx_seq_id, tx_seq_id);
        $display("T=%0t %s Config: SIZE=%0d, OFFSET=%0d", $time, tag, config_size, config_offset);

        // RX
        $display("T=%0t %s RX: data=0x%08h, offset=%0d, size=%0d",
                 $time, tag, rx_data, rx_offset, rx_size);

        // TX (si no aplica, se muestra N/A)
        if (tx_seq_id == 0 && tx_size == 0)
            $display("T=%0t %s TX: N/A (aún no emparejado)", $time, tag);
        else
            $display("T=%0t %s TX: data=0x%08h, offset=%0d, size=%0d",
                     $time, tag, tx_data, tx_offset, tx_size);

        $display("T=%0t %s ============================================", $time, tag);
    endfunction
endclass


// Definir mailbox específico para checker_result
typedef mailbox #(checker_result) checker_result_mbx;

//================================================================================
// Clase principal del Checker
//================================================================================
class aligner_checker;

    //==============================
    // MAILBOXES
    //==============================
    trans_apb_in_mbx    apb_config_mbx;   // Config APB desde generador
    trans_rx_in_mbx     rx_in_mbx;        // RX del generador
    trans_rx_out_mbx    rx_out_mbx;       // Respuesta RX del monitor
    trans_tx_out_mbx    tx_out_mbx;       // TX del monitor
    checker_result_mbx  chk_scb_mbx;      // Hacia scoreboard

    //==============================
    // ESTADO DE CONFIG
    //==============================
    localparam int ALGN_DATA_WIDTH = 32;      // ← antes era 'parameter'
    localparam int DATA_BYTES      = ALGN_DATA_WIDTH/8; // 4
    logic [2:0] current_size   = 1; // reset
    logic [1:0] current_offset = 0; // reset

    //==============================
    // COLAS / ESTADÍSTICAS
    //==============================
    byte unsigned golden_fifo[$];   // bytes en orden de llegada

    // Emparejamiento RX↔TX para reportes
    typedef struct {                 // ← antes era 'struct packed'
        int         seq;
        trans_rx_in rx;              // handle de clase permitido en struct *unpacked*
    } rx_item_t;

    rx_item_t rx_for_tx_q[$];       // RX legales pendientes de emparejar con un TX

    // Contadores
    int total_checks = 0;
    int passed_checks = 0;
    int failed_checks = 0;
    int illegal_transfers_detected = 0;
    int alignment_checks = 0;

    // Secuencia de RX / TX
    int rx_seq_counter = 0;
    int tx_seq_counter = 0;

    //==============================
    // UTILIDADES
    //==============================
    function bit validate_rx_transfer(logic [1:0] offset, logic [2:0] size);
        if (!(size inside {1,2,4})) return 0;
        return (((DATA_BYTES + offset) % size) == 0);
    endfunction

    function void push_rx_bytes_to_golden(trans_rx_in rx);
        byte unsigned bytes[DATA_BYTES];
        bytes[0] = rx.md_rx_data[7:0];
        bytes[1] = rx.md_rx_data[15:8];
        bytes[2] = rx.md_rx_data[23:16];
        bytes[3] = rx.md_rx_data[31:24];
        for (int i = 0; i < rx.md_rx_size; i++) begin
            int idx = rx.md_rx_offset + i;
            if (idx < DATA_BYTES)
                golden_fifo.push_back(bytes[idx]);
        end
    endfunction

    function logic [31:0] peek_expected_word();
        logic [31:0] w = 32'h0;
        for (int i = 0; i < current_size; i++) begin
            byte unsigned bi = golden_fifo[i];
            w[8*(current_offset + i) +: 8] = bi;
        end
        return w;
    endfunction

    function void commit_bytes();
        for (int i = 0; i < current_size; i++) void'(golden_fifo.pop_front());
    endfunction

    //==============================
    // CHECKS
    //==============================
    function checker_result check_illegal_transfer(
        trans_rx_in rx_trans,
        trans_rx_out rx_resp,
        int rx_seq_id
    );
        checker_result r = new();
        bit legal;
        r.timestamp        = $realtime;
        r.test_description = "Illegal Transfer Detection";
        r.rx_seq_id        = rx_seq_id;
        r.tx_seq_id        = 0;
        r.rx_data          = rx_trans.md_rx_data;
        r.rx_offset        = rx_trans.md_rx_offset;
        r.rx_size          = rx_trans.md_rx_size;
        r.tx_data          = '0;
        r.tx_offset        = '0;
        r.tx_size          = '0;
        r.config_size      = current_size;
        r.config_offset    = current_offset;

        legal = validate_rx_transfer(rx_trans.md_rx_offset, rx_trans.md_rx_size);

        if (!legal) begin
            if (rx_resp.md_rx_err == 1) begin
                r.test_passed   = 1;
                r.error_message = "Illegal transfer correctly detected";
                illegal_transfers_detected++;
            end else begin
                r.test_passed   = 0;
                r.error_message = $sformatf("Illegal transfer NOT detected (off=%0d,size=%0d)",
                                             rx_trans.md_rx_offset, rx_trans.md_rx_size);
            end
        end else begin
            if (rx_resp.md_rx_err == 0) begin
                r.test_passed   = 1;
                r.error_message = "Legal transfer correctly processed";
            end else begin
                r.test_passed   = 0;
                r.error_message = "Legal transfer flagged as error";
            end
        end
        return r;
    endfunction

    function checker_result check_alignment(
        rx_item_t rx_item,
        trans_tx_out tx_trans,
        int tx_seq_id
    );
        checker_result r = new();
        logic [31:0] expected;
        r.timestamp        = $realtime;
        r.test_description = "Data Alignment Verification";
        r.rx_seq_id        = rx_item.seq;
        r.tx_seq_id        = tx_seq_id;

        r.rx_data       = rx_item.rx.md_rx_data;
        r.rx_offset     = rx_item.rx.md_rx_offset;
        r.rx_size       = rx_item.rx.md_rx_size;
        r.tx_data       = tx_trans.md_tx_data;
        r.tx_offset     = tx_trans.md_tx_offset;
        r.tx_size       = tx_trans.md_tx_size;
        r.config_size   = current_size;
        r.config_offset = current_offset;

        if (tx_trans.md_tx_size   != current_size)  begin
            r.test_passed = 0;
            r.error_message = $sformatf("TX size mismatch: expected %0d, got %0d",
                                        current_size, tx_trans.md_tx_size);
            return r;
        end
        if (tx_trans.md_tx_offset != current_offset) begin
            r.test_passed = 0;
            r.error_message = $sformatf("TX offset mismatch: expected %0d, got %0d",
                                        current_offset, tx_trans.md_tx_offset);
            return r;
        end
        if (!tx_trans.md_tx_valid) begin
            r.test_passed = 0;
            r.error_message = "TX valid not asserted";
            return r;
        end
        if (golden_fifo.size() < current_size) begin
            r.test_passed = 0;
            r.error_message = $sformatf("Not enough RX bytes for TX: need %0d, have %0d",
                                        current_size, golden_fifo.size());
            return r;
        end

        expected = peek_expected_word();
        if (expected !== tx_trans.md_tx_data) begin
            r.test_passed = 0;
            r.error_message = $sformatf("TX data mismatch: expected 0x%08h, got 0x%08h",
                                        expected, tx_trans.md_tx_data);
            return r;
        end

        commit_bytes();
        r.test_passed   = 1;
        r.error_message = "Alignment check passed";
        return r;
    endfunction

    //==============================
    // HILOS
    //==============================
    task monitor_apb_config();
        forever begin
            trans_apb_in apb_trans;
            apb_config_mbx.get(apb_trans);
            if (apb_trans.pwrite && (apb_trans.paddr == 16'h0000)) begin
                logic [2:0] new_size   = apb_trans.pwdata[2:0];
                logic [1:0] new_offset = apb_trans.pwdata[9:8];
                if (new_size inside {1,2,4}) begin
                    current_size   = new_size;
                    current_offset = new_offset;
                    $display("T=%0t [Checker] Configuration updated: SIZE=%0d, OFFSET=%0d",
                             $time, current_size, current_offset);
                end
            end
        end
    endtask

    task check_rx_transfers();
        checker_result r_il;
        forever begin
            trans_rx_in  rx_trans;
            trans_rx_out rx_resp;

            rx_in_mbx.get(rx_trans);
            rx_out_mbx.get(rx_resp);

            rx_seq_counter++;

            r_il = check_illegal_transfer(rx_trans, rx_resp, rx_seq_counter);

            if (validate_rx_transfer(rx_trans.md_rx_offset, rx_trans.md_rx_size) &&
                (rx_resp.md_rx_err == 1'b0)) begin
                rx_item_t it;        // declaración antes de usar
                push_rx_bytes_to_golden(rx_trans);
                it.seq = rx_seq_counter;
                it.rx  = rx_trans;
                rx_for_tx_q.push_back(it);
            end

            total_checks++;
            if (r_il.test_passed) passed_checks++; else failed_checks++;
            r_il.print("[Checker]");
            chk_scb_mbx.put(r_il);
        end
    endtask

    task check_tx_transfers();
        checker_result r_tx;
        forever begin
            trans_tx_out tx_trans;
            rx_item_t    rx_item;
            tx_out_mbx.get(tx_trans);
            tx_seq_counter++;

            if (rx_for_tx_q.size() == 0) begin
                r_tx = new();
                r_tx.timestamp        = $realtime;
                r_tx.test_description = "TX without prior legal RX";
                r_tx.test_passed      = 0;
                r_tx.error_message    = "No matching legal RX in queue";
                r_tx.rx_seq_id        = 0;
                r_tx.tx_seq_id        = tx_seq_counter;
                r_tx.tx_data          = tx_trans.md_tx_data;
                r_tx.tx_offset        = tx_trans.md_tx_offset;
                r_tx.tx_size          = tx_trans.md_tx_size;
                r_tx.config_size      = current_size;
                r_tx.config_offset    = current_offset;

                total_checks++; failed_checks++;
                r_tx.print("[Checker]");
                chk_scb_mbx.put(r_tx);
                continue;
            end

            rx_item = rx_for_tx_q.pop_front();

            r_tx = check_alignment(rx_item, tx_trans, tx_seq_counter);

            total_checks++; alignment_checks++;
            if (r_tx.test_passed) passed_checks++; else failed_checks++;
            r_tx.print("[Checker]");
            chk_scb_mbx.put(r_tx);
        end
    endtask

    task run();
        $display("T=%0t [Checker] Iniciado", $time);
        fork
            monitor_apb_config();
            check_rx_transfers();
            check_tx_transfers();
        join_none
    endtask

    function void print_statistics();
        real pass_rate;
        $display("========================================");
        $display("       CHECKER STATISTICS");
        $display("========================================");
        $display("Total Checks:              %0d", total_checks);
        $display("Passed Checks:             %0d", passed_checks);
        $display("Failed Checks:             %0d", failed_checks);
        $display("Illegal Transfers Detected: %0d", illegal_transfers_detected);
        $display("Alignment Checks:          %0d", alignment_checks);
        pass_rate = (total_checks>0) ?
            (real'(passed_checks)/real'(total_checks))*100.0 : 0.0;
        $display("Pass Rate:                 %0.2f%%", pass_rate);
        $display("========================================");
    endfunction

endclass  

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
        $fwrite(csv_file, "RX_Seq,TX_Seq,");              // <-- NUEVO
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
        $fwrite(csv_file, "%0t,", result.timestamp);
        $fwrite(csv_file, "%s,", result.test_passed ? "PASS" : "FAIL");
        $fwrite(csv_file, "\"%s\",", result.test_description);
        $fwrite(csv_file, "\"%s\",", result.error_message);

        // NUEVO: secuencias
        $fwrite(csv_file, "%0d,", result.rx_seq_id);
        $fwrite(csv_file, "%0d,", result.tx_seq_id);

        // Config
        $fwrite(csv_file, "%0d,", result.config_size);
        $fwrite(csv_file, "%0d,", result.config_offset);

        // RX
        $fwrite(csv_file, "0x%08h,", result.rx_data);
        $fwrite(csv_file, "%0d,", result.rx_offset);
        $fwrite(csv_file, "%0d,", result.rx_size);

        // TX (N/A si no aplica)
        if (result.tx_seq_id == 0 && result.tx_size == 0) begin
            $fwrite(csv_file, "NA,NA,NA,");
        end else begin
            $fwrite(csv_file, "0x%08h,", result.tx_data);
            $fwrite(csv_file, "%0d,", result.tx_offset);
            $fwrite(csv_file, "%0d,", result.tx_size);
        end

        // Contadores (si los usas)
        $fwrite(csv_file, "%0d,", result.checks_passed);
        $fwrite(csv_file, "%0d\n", result.checks_failed);
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
        $display("Secuencias:       RX=%0d  TX=%0d", result.rx_seq_id, result.tx_seq_id);
        if (!result.test_passed) $display("Error:            %s", result.error_message);
        $display("--------------------------------------------------------------------------------");
        $display("Config:           SIZE=%0d, OFFSET=%0d", result.config_size, result.config_offset);
        $display("RX:               data=0x%08h, offset=%0d, size=%0d",
                result.rx_data, result.rx_offset, result.rx_size);
        if (result.tx_seq_id == 0 && result.tx_size == 0)
            $display("TX:               N/A (aún no emparejado)");
        else
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

//================================================================================
// Módulo en el que se define el ambiente
//================================================================================

// Se incluyen archivos con transactores que debe contener el ambiente

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
        md_tx_driver_0  = new;
        md_tx_monitor_0 = new;
        md_tx_agent_0   = new;
        apb_agent_0 = new;
        apb_driver_0 = new;
        apb_monitor_0 = new;
        aligner_checker_0 = new;
        scoreboard_0 = new;

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


   endfunction

    //--------------------------------------------------
    // TASK: connect
    // Conectar todas las interfaces y mailboxes
    //--------------------------------------------------
    virtual task connect();
        $display("T=%0t [Environment] Conectando interfaces...", $time);
        
        // Verificar que las interfaces estén asignadas
        if (md_rx_vif == null) begin
            $display("ERROR CRÍTICO: md_rx_vif es null en environment");
            $finish;
        end
        if (md_tx_vif == null) begin
            $display("ERROR CRÍTICO: md_tx_vif es null en environment");
            $finish;
        end
        if (apb_vif == null) begin
            $display("ERROR CRÍTICO: apb_vif es null en environment");
            $finish;
        end
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
        $display("T=%0t [Environment] Conexiones completadas", $time);
    endtask



    virtual task run();
        $display("T=%0t [Environment] Iniciando ambiente...", $time);
        

        // Primero conectar tiodo
        connect();
        
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
      
//================================================================================
// Módulo en el que se define el test
//================================================================================

// Se incluyen archivos necesarios

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
      
//================================================================================
// Testbench Top 
//================================================================================

`timescale 1ns/1ps

module tb_aligner;

    reg clk;
    reg reset_n;
    
    parameter CLK_PERIOD = 10;  

    initial begin
        clk <= 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end
    
    //--------------------------------------------------
    // INTERFACES
    //--------------------------------------------------
    apb_interface apb_if(.pclk(clk), .preset_n(reset_n));
    md_rx_interface md_rx_if(.clk(clk), .reset_n(reset_n));
    md_tx_interface md_tx_if(.clk(clk), .reset_n(reset_n));

    //--------------------------------------------------
    // DUT 
    //--------------------------------------------------
    cfs_aligner #(
        .ALGN_DATA_WIDTH(32),
        .FIFO_DEPTH(8)
    ) dut (
        // Señales globales
        .clk(clk),
        .reset_n(reset_n),
        
        // Interface APB
        .paddr(apb_if.paddr),
        .pwrite(apb_if.pwrite),
        .psel(apb_if.psel),
        .penable(apb_if.penable),
        .pwdata(apb_if.pwdata),
        .pready(apb_if.pready),
        .prdata(apb_if.prdata),
        .pslverr(apb_if.pslverr),
        
        // Interface MD_RX
        .md_rx_valid(md_rx_if.md_rx_valid),
        .md_rx_data(md_rx_if.md_rx_data),
        .md_rx_offset(md_rx_if.md_rx_offset),
        .md_rx_size(md_rx_if.md_rx_size),
        .md_rx_ready(md_rx_if.md_rx_ready),
        .md_rx_err(md_rx_if.md_rx_err),
        
        // Interface MD_TX
        .md_tx_valid(md_tx_if.md_tx_valid),
        .md_tx_data(md_tx_if.md_tx_data),
        .md_tx_offset(md_tx_if.md_tx_offset),
        .md_tx_size(md_tx_if.md_tx_size),
        .md_tx_ready(md_tx_if.md_tx_ready),
        .md_tx_err(md_tx_if.md_tx_err),
        
        // Interrupción
        .irq()
    );

  
    test t0;

    initial begin
        reset_n = 0;
        $display("T=%0t [TB] Inicializando testbench...", $time);

        repeat(2) @(posedge clk);
        reset_n <= 1;
        
        $display("T=%0t [TB] Reset liberado, iniciando test...", $time);
        
        t0 = new();
        t0.md_rx_vif = md_rx_if;
        t0.md_tx_vif = md_tx_if;
        t0.apb_vif = apb_if;

        // VERIFICAR que las interfaces se asignaron correctamente
        if (t0.md_rx_vif == null) begin
            $display("ERROR: md_rx_vif no asignada");
            $finish;
        end
        if (t0.md_tx_vif == null) begin
            $display("ERROR: md_tx_vif no asignada");
            $finish;
        end
        if (t0.apb_vif == null) begin
            $display("ERROR: apb_vif no asignada");
            $finish;
        end
        @(posedge clk);
        // Ejecutar test
        t0.run();
        
        // Esperar a que el test termine
        #10000;
        $display("T=%0t [TB] Test completado", $time);
        $finish;
    end
    
    //--------------------------------------------------
    // VOLCADO DE SEÑALES
    //--------------------------------------------------
    initial begin
        $dumpvars;
        $dumpfile("dump.vcd");
    end
    
    //--------------------------------------------------
    // TIMEOUT DE SEGURIDAD
    //--------------------------------------------------
    initial begin
        #50000; // 50us timeout
        $display("T=%0t [TB] TIMEOUT: Simulación muy larga", $time);
        $finish;
    end

endmodule
      





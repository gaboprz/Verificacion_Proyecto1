
class trans_tx_in;
  rand bit md_tx_ready;
  rand bit md_tx_err;

    function void print(string tag="");
        $display("T=%0t [%s] md_tx_ready=0x%0h, md_tx_err=0x%0h", 
                 $time, tag, md_tx_ready, md_tx_err);  // ← tag agregado
    endfunction

endclass

class trans_tx_out;
  bit          md_tx_valid;
  logic [31:0] md_tx_data;
  logic [1:0]  md_tx_offset;
  logic [2:0]  md_tx_size;

    function void print(string tag="");
        $display("T=%0t [%s] md_tx_valid=0x%0h, md_tx_data=0x%0h, md_tx_offset=0x%0h, md_tx_size=0x%0h", 
                 $time, tag, md_tx_valid, md_tx_data, md_tx_offset, md_tx_size);
    endfunction
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
        input clk,           // El monitor SOLO LEE clk
        input reset_n        // El monitor SOLO LEE reset
    );
    
    // Para el DUT - recibe de driver y envía a monitor
    modport DUT (
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

    //Tamaños válidos
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
    mailbox seq_drv_tx_mbx;
    event drv_tx_done;
    task run();
        $display("T=%0t [%s] driver iniciado", $time);

        // Inicializar señales
        vif.md_tx_ready <= 0;
        vif.md_tx_err <= 0;

        //Esperar reset 
        wait(vif.reset_n == 1);

        forever begin
            trans_tx_in item_dv_tx=new();
            
            //obtener datos del generador
            seq_drv_tx_mbx.get(item_dv_tx);
            item_dv_tx.print("Driver");
            //Asignacion de datos que ingresan al dut
            vif.md_tx_ready <= item_dv_tx.md_tx_ready;
            vif.md_tx_err <= item_dv_tx.md_tx_err;

            @(posedge vif.clk);
            ->drv_tx_done;
        end
    endtask

endclass

class md_tx_monitor;
    // Conexión a la interface
    virtual md_tx_interface.MONITOR vif;
    mailbox mon_scb_tx_mbx;
    
    // Identificador
    string name;

    task run();
        $display("T=%0t [%s] Monitor iniciado", $time);
        
        // Esperar que el reset termine
        wait(vif.reset_n == 1);
        
        forever begin
            // Esperar transferencia válida del DUT
            // Según documentación del Aligner:
            // A transfer ends when VALID is 1 and READY is 1
            do begin
                @(posedge vif.clk);
            end while (!(vif.md_tx_valid && vif.md_tx_ready));
            
            // Capturar transacción
            trans_tx_out item_mon_tx = new();
            item_mon_tx.md_tx_valid   = vif.md_tx_valid;
            item_mon_tx.md_tx_data    = vif.md_tx_data;
            item_mon_tx.md_tx_offset  = vif.md_tx_offset;
            item_mon_tx.md_tx_size    = vif.md_tx_size;
            
            // Enviar al scoreboard
            mon_scb_tx_mbx.put(item_mon_tx);
            
        end
    endtask
endclass
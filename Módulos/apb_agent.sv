//================================================================================
// Módulo en el que se define la interfaz para interactuar con el "Register File", 
// además de que se define el agente, el driver y el monitor para la interacción 
// con esta interfaz
//================================================================================

// Se incluye el archivo donde están definidos los tipos de paquetes
`include "transactions.sv"



//================================================================================
// Gané la ruleta!!! atte: Amanda Hernández carnet 2020023645 :)
//================================================================================



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

  function void print(string tag="");
    $display("T=%0t %s pready=0x%0h, prdata=0x%0h, pslverr=0x%0h", 
             $time,tag, pready, prdata, pslverr);
  endfunction

endclass


interface apb_interface (input logic pclk, input logic preset_n);
    //--------------------------------------------------
    // SEÑALES APB (iguales a las del core)
    //--------------------------------------------------
    logic [15:0] paddr;     // Dirección (16 bits)
    logic        pwrite;    // 1=Escritura, 0=Lectura
    logic        psel;      // Selección del slave
    logic        penable;   // Habilitación
    logic [31:0] pwdata;    // Datos de escritura
    
    logic        pready;    // Ready del slave
    logic [31:0] prdata;    // Datos de lectura  
    logic        pslverr;   // Error del slave

    // --------------------------------------------------
    // MODPORTS
    // --------------------------------------------------
    
    // Para el DRIVER - controla las señales hacia el DUT
    modport DRIVER (
        output paddr, pwrite, psel, penable, pwdata,
        input  pclk, preset_n
    );
    
    // Para el MONITOR - solo lee todas las señales
    modport MONITOR (
        input paddr, pwrite, psel, penable, pwdata, pready, prdata, pslverr,
        input pclk, preset_n
    );
    
    // Para el DUT - recibe las señales del driver y envía respuestas
    modport DUT (
        input  paddr, pwrite, psel, penable, pwdata,
        output pready, prdata, pslverr,
        input  pclk, preset_n
    );

    // --------------------------------------------------
    // ASSERTIONS 
    // --------------------------------------------------

    // penable solo puede ser alto si psel está alto
    property valid_penable;
        @(posedge pclk) disable iff (!preset_n)
        penable |-> psel;
    endproperty
    ASSERT_VALID_PENABLE: assert property (valid_penable);

    // Las señales deben mantenerse estables durante la transferencia
    property stable_signals;
        @(posedge pclk) disable iff (!preset_n)
        (psel && !penable) |=> $stable(paddr) && $stable(pwrite) && $stable(pwdata);
    endproperty
    ASSERT_STABLE_SIGNALS: assert property (stable_signals);

    // pready no debe cambiar durante penable
    property stable_pready;
        @(posedge pclk) disable iff (!preset_n)
        penable |-> $stable(pready);
    endproperty
    ASSERT_STABLE_PREADY: assert property (stable_pready);

endinterface



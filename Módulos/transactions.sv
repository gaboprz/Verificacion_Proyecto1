//================================================================================
// Módulo en el que se definen los distintos paquetes / transacciones
// que se usan en el ambiente.
//================================================================================

// Incluye paquetes de UVM
`include "uvm_pkg_imports.sv" 



//================================================================================
// Clase de transacción / paquete APB  de entrada.
// Pasa del sequencer al Driver y de ahí se usa como la entrada a la interfaz APB.
//================================================================================

class trans_apb_in extends uvm_sequence_item;
  `uvm_object_utils(trans_apb_in)

  // Atributos
  rand bit          psel;     
  rand bit          penable;  
  rand bit          pwrite;   
  rand logic [15:0] paddr;    
  rand logic [31:0] pwdata;   

  // Constructor
  function new(string name = "trans_apb_in");
    super.new(name);
  endfunction

  // Constraints



  // Funciones


  // Macros de campos 
  `uvm_field_int(psel,   UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(penable,UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(pwrite, UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(paddr,  UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(pwdata, UVM_ALL_ON | UVM_HEX)

endclass


//================================================================================
// Clase de transacción / paquete APB  de salida.
// Sale de la interfaz APB hacia el monitor, de ahí va al scoreboard
//================================================================================

class trans_apb_out extends uvm_sequence_item;
  `uvm_object_utils(trans_apb_out)

  // Atributos
  rand bit          pready;   
  rand logic [31:0] prdata;   
  rand bit          pslverr;  

  // Constructor
  function new(string name = "trans_apb_out");
    super.new(name);
  endfunction

  // Constraints


  // Funciones


  // Macros de campos
  `uvm_field_int(pready,  UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(prdata,  UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(pslverr, UVM_ALL_ON | UVM_HEX)

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO RX de entrada
// Pasa del sequencer al driver y de ahí se usa como la entrada a la interfaz MB de FIFO RX.
//================================================================================
class trans_rx_in extends uvm_sequence_item;
  `uvm_object_utils(trans_rx_in)

  // Atributos
  rand bit          md_rx_valid;
  rand logic [31:0] md_rx_data;
  rand logic [1:0]  md_rx_offset;
  rand logic [2:0]  md_rx_size;

  // Constructor
  function new(string name = "trans_rx_in");
    super.new(name);
  endfunction

  // Constraints


  // Funciones


  // Macros de campos 
  `uvm_field_int(md_rx_valid,  UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(md_rx_data,   UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(md_rx_offset, UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(md_rx_size,   UVM_ALL_ON | UVM_HEX)

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO RX de salida
// Sale de la interfaz MB de FIFO RX hacia el monitor, de ahí va al scoreboard
//================================================================================

class trans_rx_out extends uvm_sequence_item;
  `uvm_object_utils(trans_rx_out)

  // Atributos
  rand bit md_rx_ready;
  rand bit md_rx_err;

  // Constructor
  function new(string name = "trans_rx_out");
    super.new(name);
  endfunction

  // Constraints


  // Funciones


  // Macros de campos 
  `uvm_field_int(md_rx_ready, UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(md_rx_err,   UVM_ALL_ON | UVM_HEX)

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO TX de entrada
// Pasa del sequencer al driver y de ahí se usa como la entrada a la interfaz MB de FIFO TX.
//================================================================================

class trans_tx_in extends uvm_sequence_item;
  `uvm_object_utils(trans_tx_in)

  // Atributos
  rand bit md_tx_ready;
  rand bit md_tx_err;

  // Constructor
  function new(string name = "trans_tx_in");
    super.new(name);
  endfunction

  // Constraints


  // Funciones


  // Macros de campos 
  `uvm_field_int(md_tx_ready, UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(md_tx_err,   UVM_ALL_ON | UVM_HEX)

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO TX de salida
// Sale de la interfaz MB de FIFO TX hacia el monitor, de ahí va al scoreboard
//================================================================================

class trans_tx_out extends uvm_sequence_item;
  `uvm_object_utils(trans_tx_out)

  // Atributos
  rand bit          md_tx_valid;
  rand logic [31:0] md_tx_data;
  rand logic [1:0]  md_tx_offset;
  rand logic [2:0]  md_tx_size;

  // Constructor
  function new(string name = "trans_tx_out");
    super.new(name);
  endfunction

  // Constraints


  // Funciones


  // Macros de campos 
  `uvm_field_int(md_tx_valid,  UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(md_tx_data,   UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(md_tx_offset, UVM_ALL_ON | UVM_HEX)
  `uvm_field_int(md_tx_size,   UVM_ALL_ON | UVM_HEX)

endclass

//================================================================================
// Módulo en el que se definen los distintos paquetes / transacciones
// que se usan en el ambiente.
//================================================================================

//================================================================================
// Clase de transacción / paquete APB de entrada.
//================================================================================

class trans_apb_in;

  rand bit          psel;     
  rand bit          penable;  
  rand bit          pwrite;   
  rand logic [15:0] paddr;    
  rand logic [31:0] pwdata;   

  function void print(string tag="");
    $display("T=%0t %s psel=0x%0h, penable=0x%0h, pwrite=0x%0h, paddr=0x%0h, pwdata=0x%0h", 
             $time, psel, penable, pwrite, paddr, pwdata);
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
             $time, pready, prdata, pslverr);
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

  function void print(string tag="");
    $display("T=%0t %s md_rx_valid=0x%0h, md_rx_data=0x%0h, md_rx_offset=0x%0h, md_rx_size=0x%0h", 
             $time, md_rx_valid, md_rx_data, md_rx_offset, md_rx_size);
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
             $time, md_rx_ready, md_rx_err);
  endfunction

endclass


//================================================================================
// Clase de transacción / paquete MB de FIFO TX de entrada
//================================================================================

class trans_tx_in;

  rand bit md_tx_ready;
  rand bit md_tx_err;

  function void print(string tag="");
    $display("T=%0t %s md_tx_ready=0x%0h, md_tx_err=0x%0h", 
             $time, md_tx_ready, md_tx_err);
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

  function void print(string tag="");
    $display("T=%0t %s md_tx_valid=0x%0h, md_tx_data=0x%0h, md_tx_offset=0x%0h, md_tx_size=0x%0h", 
             $time, md_tx_valid, md_tx_data, md_tx_offset, md_tx_size);
  endfunction

endclass
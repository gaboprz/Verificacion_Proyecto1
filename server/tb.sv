//================================================================================
// Testbench Top 
//================================================================================

`timescale 1ns/1ps

`include "test.sv"
`include "cfs_aligner.v"  
`include "cfs_synch.v"
`include "cfs_synch_fifo.v"
`include "cfs_rx_ctrl.v"
`include "cfs_ctrl.v"
`include "cfs_tx_ctrl.v"
`include "cfs_edge_detect.v"
`include "cfs_regs.v"
`include "cfs_aligner_core.v"

module tb_aligner;

    reg clk;
    reg reset_n;
    
    parameter CLK_PERIOD = 10;  

    always #(CLK_PERIOD/2) clk = ~clk;
    
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

        clk <= 0;
        reset_n <= 0;

        #100;
        reset_n <= 1;
        
        $display("T=%0t [TB] Reset liberado, iniciando test...", $time);
        
        t0 = new();
        t0.md_rx_vif = md_rx_if;
        t0.md_tx_vif = md_tx_if;
        t0.apb_vif = apb_if;
        
        // Ejecutar test
        t0.run();
        
        // Esperar a que el test termine
        #50000;
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
        #1000000; // 1ms timeout
        $display("T=%0t [TB] TIMEOUT: Simulación muy larga", $time);
        $finish;
    end

endmodule
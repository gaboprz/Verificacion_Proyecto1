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

// =================================================================================
// Definición de número de transacciones
// =================================================================================

typedef enum {
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
typedef mailbox #(instr_agente_APB) comando_test_apb_mbx;
typedef mailbox #(cantidad_inst_agente_APB) num_trans_test_apb_mbx;


// =================================================================================
// Definición de tipos de instrucción 
// =================================================================================

typedef enum {
    APB_CONFIGURACION_INICIAL,    // Secuencia de arranque (1 vez) LISTO
    APB_CONFIG_VALIDA,            // Múltiples configs válidas  LISTO
    APB_CONFIG_INVALIDA,          // Múltiples configs inválidas LISTO
    APB_MONITOREO_ESTADO,         // Monitoreo continuo del estado
    APB_GESTION_INTERRUPT,        // Secuencia de  IRQ (1 vez)
    APB_STRESS_TEST,              // Pruebas de estrés 
    APB_SINGLE_OPERATION          // Operación única para debug
} instr_agente_APB;

// =================================================================================
// Agente APB Híbrido Inteligente
// =================================================================================

class apb_agent;
    // Mailboxes
    trans_apb_in_mbx                 gen_drv_apb_mbx;
    trans_apb_in_mbx                 gen_chk_apb_mbx;
    comando_test_apb_mbx             test_agt_apb_mbx;
    num_trans_test_apb_mbx           test_agt_num_tran_apb_mbx;
    
    // Variables de control
    instr_agente_APB                 instruccion_apb;
    cantidad_inst_agente_APB         num_trans_apb;
    event                            drv_apb_done;
    
    // Direcciones de registros
    localparam bit [15:0] CTRL_ADDR   = 16'h0000;
    localparam bit [15:0] STATUS_ADDR = 16'h000C;
    localparam bit [15:0] IRQEN_ADDR  = 16'h00F0;
    localparam bit [15:0] IRQ_ADDR    = 16'h00F4;
    localparam bit [15:0] ILLEGAL_ADDR_1 = 16'h0004;
    localparam bit [15:0] ILLEGAL_ADDR_2 = 16'h00F8;
    
    // Array de configuraciones críticas 
    localparam bit [31:0] CONFIG_BASES [7] = '{
    32'h00000001, // SIZE=1, OFFSET=0
    32'h00000002, // SIZE=2, OFFSET=0  
    32'h00000004, // SIZE=4, OFFSET=0
    32'h00000101, // SIZE=1, OFFSET=1
    32'h00000201, // SIZE=1, OFFSET=2
    32'h00000301  // SIZE=1, OFFSET=3
    32'h00000202, // SIZE=2, OFFSET=0  
    };

    function int obtener_num_trans_apb();
        case(num_trans_apb)
            APB_CINCO:     return 5;
            APB_DIEZ:      return 10;
            APB_QUINCE:    return 15;
            APB_TREINTA:   return 30;
            APB_CINCUENTA: return 50;
            default:       return 1;
        endcase
    endfunction

    // Funció para generar configuraciones CTRL
    function bit [31:0] generar_config_ctrl(bit incluir_clear = 0);
        bit [2:0] size;
        bit [1:0] offset;
        bit clear_bit;
        
        // Generar combinaciones válidas
        size = ($urandom % 3); // 0,1,2
        case(size)
            0: size = 3'h1;  // 1 byte
            1: size = 3'h2;  // 2 bytes  
            2: size = 3'h4;  // 4 bytes
        endcase
        
        // Offset compatible
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
            $display("T=%0t [Agent APB] Esperando instrucciones del test", $time);
            test_agt_apb_mbx.get(instruccion_apb);
            test_agt_num_tran_apb_mbx.get(num_trans_apb);
            $display("T=%0t [Agent APB] Instrucción: %s", $time, instruccion_apb.name());

            case(instruccion_apb)
                // =============================================================
                // MODO 1: Configuración inicial 
                // =============================================================
                APB_CONFIGURACION_INICIAL: begin
                    $display("T=%0t [APB] Ejecutando secuencia de configuración inicial", $time);
                    
                    // 1. Configurar CTRL
                    trans_apb_in item_ctrl = new();
                    item_ctrl.psel = 1'b1; 
                    item_ctrl.penable = 1'b0; 
                    item_ctrl.pwrite = 1'b1;
                    item_ctrl.paddr = CTRL_ADDR;
                    item_ctrl.pwdata = generar_config_ctrl(0);

                    //El Driver hacer la transición a penable=1 en el ciclo siguiente!!!!!!!
                    gen_drv_apb_mbx.put(item_ctrl); 
                    gen_chk_apb_mbx.put(item_ctrl);
                    item_ctrl.print("[APB] CONFIG_INICIAL - CTRL");
                    @(drv_apb_done);

                    // 2. Configurar IRQEN
                    trans_apb_in item_irqen = new();
                    item_irqen.psel = 1'b1; 
                    item_irqen.penable = 1'b0; 
                    item_irqen.pwrite = 1'b1;
                    item_irqen.paddr = IRQEN_ADDR;
                    item_irqen.pwdata = 32'h0000001F;
                    gen_drv_apb_mbx.put(item_irqen); 
                    gen_chk_apb_mbx.put(item_irqen);
                    item_irqen.print("[APB] CONFIG_INICIAL - IRQEN");
                    @(drv_apb_done);

                    $display("T=%0t [APB] Configuración inicial completada", $time);
                end

                // =============================================================
                // MODO 2: Configuraciones válidas
                // =============================================================
                APB_CONFIG_VALIDA: begin
                    int num_configs = obtener_num_trans_apb();
                    $display("T=%0t [APB] Probando %0d configuraciones válidas diferentes", $time, num_configs);
                    
                    for (int i = 0; i < num_configs; i++) begin
                        trans_apb_in item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b1;
                        item.paddr = CTRL_ADDR;
                        
                        // Diferente configuración en cada iteración
                        if (i < 7) begin
                            // Primeras 6 iteraciones
                            item.pwdata = CONFIG_BASES[i];
                        end else begin
                            // Iteraciones adicionales
                            item.pwdata = generar_config_ctrl(i % 2); // Alternar CLEAR
                        end
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf("[APB] CONFIG_VALIDA %0d", i+1));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 3:Configuraciones invalidas
                // =============================================================
                APB_CONFIG_INVALIDA: begin
                    int num_errores = obtener_num_trans_apb();
                    $display("T=%0t [APB] Probando %0d configuraciones inválidas", $time, num_errores);
                    
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
                    
                    for (int i = 0; i < num_errores; i++) begin
                        trans_apb_in item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b1;
                        item.paddr = CTRL_ADDR;
                        
                        item.pwdata = todos_los_errores[i % 8];
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf("[APB] Configuracion invalida %0d", i+1));
                        @(drv_apb_done);
                    end
                end     
                default: begin
                    $display("T=%0t [APB] Usando operación por defecto", $time);
                    
                    trans_apb_in item = new();
                    item.psel = 1'b1; item.penable = 1'b0; item.pwrite = 1'b1;
                    item.paddr = CTRL_ADDR;
                    item.pwdata = generar_config_ctrl(0);
                    
                    gen_drv_apb_mbx.put(item); gen_chk_apb_mbx.put(item);
                    item.print("[APB] DEFAULT");
                    @(drv_apb_done);
                end
            endcase
            
            $display("T=%0t [Agent APB] Ejecución completada: %s", $time, instruccion_apb.name());
        end
    endtask
endclass



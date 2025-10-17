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
    APB_ASSERT_VALID_PENABLE: assert property (valid_penable);  // ← NOMBRE CORREGIDO

    property stable_signals;
        @(posedge pclk) disable iff (!preset_n)
        (psel && !penable) |=> $stable(paddr) && $stable(pwrite) && $stable(pwdata);
    endproperty
    APB_ASSERT_STABLE_SIGNALS: assert property (stable_signals);  // ← NOMBRE CORREGIDO

    property stable_pready;
        @(posedge pclk) disable iff (!preset_n)
        penable |-> $stable(pready);
    endproperty
    APB_ASSERT_STABLE_PREADY: assert property (stable_pready);  // ← NOMBRE CORREGIDO

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

                    $display("T=%0t [APB] Ejecutando secuencia de configuración inicial", $time);
                    
                    // 1. Configurar CTRL con una configuración válida
                    item_ctrl = new();
                    item_ctrl.psel = 1'b1; 
                    item_ctrl.penable = 1'b0; 
                    item_ctrl.pwrite = 1'b1;
                    item_ctrl.paddr = CTRL_ADDR;
                    item_ctrl.pwdata = generar_config_ctrl(0);
                    gen_drv_apb_mbx.put(item_ctrl); 
                    gen_chk_apb_mbx.put(item_ctrl);
                    item_ctrl.print("[APB] CONFIG_INICIAL - CTRL");
                    @(drv_apb_done);

                    // 2. Configurar IRQEN (habilitar todas las interrupciones)
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
                //Verificar que el Aligner acepta todas las combinaciones 
                //válidas de SIZE y OFFSET

                APB_CONFIG_VALIDA: begin
                    int num_configs = obtener_num_trans_apb();
                    $display("T=%0t [APB] Probando %0d configuraciones válidas diferentes", $time, num_configs);
                    
                    for (int i = 0; i < num_configs; i++) begin
                        trans_apb_in item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b1;
                        item.paddr = CTRL_ADDR;
                        item.pwdata = generar_config_ctrl(i % 2); // Alternar CLEAR
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf("[APB] CONFIG_VALIDA %0d", i+1));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 3:Configuraciones invalidas
                // =============================================================
                //Verificar que el Aligner rechaza correctamente configuraciones 
                //invalidas y no se corrompe con entradas incorrectas

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






                // =============================================================
                // MODO 4: ESCRIBIR IRQEN
                // =============================================================
                APB_ESCRIBIR_IRQEN: begin
                    int num_escrituras = obtener_num_trans_apb();
                    $display("T=%0t [APB] %0d escrituras a IRQEN", $time, num_escrituras);
                    
                    for (int i = 0; i < num_escrituras; i++) begin
                        trans_apb_in item = new();
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
                        item.print($sformatf("[APB] ESCRIBIR_IRQEN %0d/%0d", i+1, num_escrituras));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 5: ESCRIBIR IRQ (CLEAR)
                // =============================================================
                APB_ESCRIBIR_IRQ: begin
                    int num_escrituras = obtener_num_trans_apb();
                    $display("T=%0t [APB] %0d escrituras a IRQ (clear)", $time, num_escrituras);
                    
                    for (int i = 0; i < num_escrituras; i++) begin
                        trans_apb_in item = new();
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
                        item.print($sformatf("[APB] ESCRIBIR_IRQ %0d/%0d", i+1, num_escrituras));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 6: LEER STATUS
                // =============================================================
                APB_LEER_STATUS: begin
                    int num_lecturas = obtener_num_trans_apb();
                    $display("T=%0t [APB] %0d lecturas consecutivas de STATUS", $time, num_lecturas);
                    
                    for (int i = 0; i < num_lecturas; i++) begin
                        trans_apb_in item = new();
                        item.psel = 1'b1;
                        item.penable = 1'b0;
                        item.pwrite = 1'b0;           // LECTURA
                        item.paddr = STATUS_ADDR;     
                        item.pwdata = 32'h0;          
                        
                        gen_drv_apb_mbx.put(item);
                        gen_chk_apb_mbx.put(item);
                        
                        item.print($sformatf("[APB] LEER_STATUS %0d/%0d", i+1, num_lecturas));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 7: LEER IRQEN
                // =============================================================
                APB_LEER_IRQEN: begin
                    int num_lecturas = obtener_num_trans_apb();
                    $display("T=%0t [APB] %0d lecturas de IRQEN", $time, num_lecturas);
                    
                    for (int i = 0; i < num_lecturas; i++) begin
                        trans_apb_in item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b0;  // LECTURA
                        item.paddr = IRQEN_ADDR;
                        item.pwdata = 32'h0;
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf("[APB] LEER_IRQEN %0d/%0d", i+1, num_lecturas));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 8: LEER IRQ
                // =============================================================
                APB_LEER_IRQ: begin
                    int num_lecturas = obtener_num_trans_apb();
                    $display("T=%0t [APB] %0d lecturas de IRQ", $time, num_lecturas);
                    
                    for (int i = 0; i < num_lecturas; i++) begin
                        trans_apb_in item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = 1'b0;  // LECTURA
                        item.paddr = IRQ_ADDR;
                        item.pwdata = 32'h0;
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf("[APB] LEER_IRQ %0d/%0d", i+1, num_lecturas));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO 9: ACCESO ILEGAL
                // =============================================================
                APB_ACCESO_ILEGAL: begin
                    int num_accesos = obtener_num_trans_apb();
                    $display("T=%0t [APB] %0d accesos ilegales", $time, num_accesos);
                    
                    for (int i = 0; i < num_accesos; i++) begin
                        trans_apb_in item = new();
                        item.psel = 1'b1; 
                        item.penable = 1'b0; 
                        item.pwrite = $urandom_range(0, 1); // Lectura o escritura aleatoria
                        item.paddr = DIRECCIONES_ILEGALES[i % 6];
                        item.pwdata = $urandom();
                        
                        gen_drv_apb_mbx.put(item); 
                        gen_chk_apb_mbx.put(item);
                        item.print($sformatf("[APB] ACCESO_ILEGAL %0d/%0d", i+1, num_accesos));
                        @(drv_apb_done);
                    end
                end



                // =============================================================
                // SECUENCIA 
                // =============================================================
                APB_SECUENCIA_PERSONALIZADA: begin
                    int num_secuencias = obtener_num_trans_apb();
                    $display("T=%0t [APB] Ejecutando %0d secuencias personalizadas", $time, num_secuencias);
                    
                    for (int i = 0; i < num_secuencias; i++) begin
                        // SECUENCIA FIJA: Escribir CTRL → Leer CTRL → Leer STATUS
                        
                        // 1. ESCRIBIR configuración CTRL
                        trans_apb_in item_escritura = new();
                        item_escritura.psel = 1'b1; 
                        item_escritura.penable = 1'b0; 
                        item_escritura.pwrite = 1'b1;
                        item_escritura.paddr = CTRL_ADDR;
                        item_escritura.pwdata = generar_config_ctrl(0);
                        gen_drv_apb_mbx.put(item_escritura); 
                        gen_chk_apb_mbx.put(item_escritura);
                        item_escritura.print($sformatf("[APB] SECUENCIA %0d - Escritura CTRL", i));
                        @(drv_apb_done);
                        
                        // 2. LEER CTRL para verificar
                        trans_apb_in item_lectura = new();
                        item_lectura.psel = 1'b1; 
                        item_lectura.penable = 1'b0; 
                        item_lectura.pwrite = 1'b0;
                        item_lectura.paddr = CTRL_ADDR;
                        item_lectura.pwdata = 32'h0;
                        gen_drv_apb_mbx.put(item_lectura); 
                        gen_chk_apb_mbx.put(item_lectura);
                        item_lectura.print($sformatf("[APB] SECUENCIA %0d - Lectura CTRL", i));
                        @(drv_apb_done);
                        
                        // 3. LEER STATUS para ver estado general
                        trans_apb_in item_status = new();
                        item_status.psel = 1'b1; 
                        item_status.penable = 1'b0; 
                        item_status.pwrite = 1'b0;
                        item_status.paddr = STATUS_ADDR;
                        item_status.pwdata = 32'h0;
                        gen_drv_apb_mbx.put(item_status); 
                        gen_chk_apb_mbx.put(item_status);
                        item_status.print($sformatf("[APB] SECUENCIA %0d - Lectura STATUS", i));
                        @(drv_apb_done);
                    end
                end

                // =============================================================
                // MODO POR DEFECTO
                // =============================================================
                default: begin
                    $display("T=%0t [APB] Modo no reconocido, usando operación por defecto", $time);
                    
                    trans_apb_in item = new();
                    item.psel = 1'b1; 
                    item.penable = 1'b0; 
                    item.pwrite = 1'b1;
                    item.paddr = CTRL_ADDR;
                    item.pwdata = generar_config_ctrl(0); // Configuración simple por defecto
                    
                    gen_drv_apb_mbx.put(item); 
                    gen_chk_apb_mbx.put(item);
                    item.print("[APB] DEFAULT");
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
        $display("T=%0t [%s] Driver APB iniciado", $time, name);
        
        // Inicializar señales APB
        vif.psel    <= 1'b0;
        vif.penable <= 1'b0;
        vif.pwrite  <= 1'b0;
        vif.paddr   <= 16'h0;
        vif.pwdata  <= 32'h0;
        
        wait(vif.preset_n == 1);
        $display("T=%0t [%s] Sistema listo", $time, name);
        
        forever begin
            trans_apb_in item_drv_apb;
            
            // Obtener transacción del agente
            gen_drv_apb_mbx.get(item_drv_apb);
            item_drv_apb.print($sformatf("[%s] Transacción recibida", name));

            // --------------------------------------------------
            // FASE 1: SETUP PHASE 
            // --------------------------------------------------
             @(posedge vif.pclk);
            vif.psel    <= 1'b1;           // Activar psel
            vif.penable <= 1'b0;           // penable = 0 en SETUP
            vif.pwrite  <= item_drv_apb.pwrite;
            vif.paddr   <= item_drv_apb.paddr;
            vif.pwdata  <= item_drv_apb.pwdata;
            
            $display("T=%0t [%s] SETUP: psel=1, penable=0", $time, name);

            // --------------------------------------------------
            // FASE 2: ACCESS PHASE 
            // --------------------------------------------------
            @(posedge vif.pclk);
            vif.penable <= 1'b1;           // penable = 1 en ACCESS
            
            $display("T=%0t [%s] ACCESS: psel=1, penable=1 - DUT procesando...", $time, name);
            
            // --------------------------------------------------
            @(posedge vif.pclk);
            
            // el DUT siempre responde con pready=1 en el SIGUIENTE ciclo
            // (según la lógica de código cfs_regs.v)
            $display("T=%0t [%s] DUT respondió: pready=%0d, pslverr=%0d", 
                     $time, name, vif.pready, vif.pslverr);
            
            // --------------------------------------------------
            // FASE 3: TERMINAR TRANSACCIÓN
            // --------------------------------------------------
            vif.psel    <= 1'b0;
            vif.penable <= 1'b0;
            
            $display("T=%0t [%s] Transacción finalizada", $time, name);
            
            -> drv_apb_done;
        end
    endtask
endclass



// =================================================================================
// Monitor APB 
// =================================================================================

class apb_monitor;
    virtual apb_interface.MONITOR vif;      
    trans_apb_out_mbx           mon_chk_apb_mbx;  // Envía transacciones al checker //no usado :(
    
    string name = "APB_MONITOR";
    

    task run();
        $display("T=%0t [%s] Monitor APB iniciado", $time, name);
        
        wait(vif.preset_n == 1);
        
        forever begin
            // Esperar una transacción APB COMPLETA
            // Según protocolo: termina cuando psel=1, penable=1, pready=1
            wait(vif.psel == 1'b1 && vif.penable == 1'b1 && vif.pready == 1'b1);
            
            trans_apb_out item_mon_apb = new();
            
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


            mon_chk_apb_mbx.put(item_mon_apb);
            item_mon_apb.print($sformatf("[%s] Transacción capturada", name));
            
            $display("T=%0t [%s] Transacción enviada al checker", $time, name);
            
            // evitar duplicados
            @(posedge vif.pclk);
        end
    endtask
    
    
endclass
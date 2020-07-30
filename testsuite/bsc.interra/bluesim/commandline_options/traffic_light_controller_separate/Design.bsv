package Design;

typedef enum {RED, YELLOW, GREEN} TLstates deriving (Eq,Bits);
typedef enum {START, SHORT, LONG} TIMstates deriving (Eq, Bits);

interface Design_IFC;
    method Action   tlc         (Bool car_present, Bit#(5) long_timer_value,
                                 Bit#(5) short_timer_value);
    method TLstates farm_light  ();
    method TLstates hwy_light   ();
endinterface: Design_IFC
          
(*
    always_enabled,
    always_ready,
    CLK = "clk",
    RST_N = "reset"
*)

module mkDesign(Design_IFC);

    Reg#(TIMstates) timer_state();
    mkReg#(START)   t_timer_state(timer_state);

    Reg#(TLstates)  hwy_state();
    mkReg#(GREEN)   t_hwy_state(hwy_state);

    Reg#(TLstates)  frm_state(); 
    mkReg#(RED)     t_frm_state(frm_state);

    Reg#(Bit#(5))   timer();
    mkReg#(0)       t_timer(timer);
  
    Bool short;
    Bool long;
    Bool enable_hwy;
    Bool enable_frm;

    short           = ((timer_state == SHORT) || (timer_state == LONG));
    long            = (timer_state == LONG);
    enable_hwy      = ((frm_state == YELLOW) && short);
    enable_frm      = ((hwy_state == YELLOW) && short);
	
    method tlc (Bool car_present, Bit#(5) long_timer_value,
                Bit#(5) short_timer_value);
        action
            //Internal variable declaration and definition
            Bool frm_start_timer;
            Bool hwy_start_timer;
            Bool start_timer;

            frm_start_timer = ((frm_state == GREEN) && ((car_present == False) || long)) || 
                              ((frm_state == RED) && enable_frm);
            hwy_start_timer = ((hwy_state == GREEN) && (car_present && long)) || 
                              ((hwy_state == RED) && enable_hwy);
            start_timer     = frm_start_timer || hwy_start_timer;

            // Timer state machine
            if(start_timer) begin
                timer <= 5'd0;
                timer_state <= START;
            end else begin
                case(timer_state)
                    START:  begin
                        timer <= timer + 5'd1;
                        if(timer >= short_timer_value) begin
                            timer_state <= SHORT;
                        end
                    end
                    SHORT:  begin
                        timer <= timer + 5'd1;
                        if(timer >= long_timer_value) begin
                            timer_state <= LONG;
                        end
                    end
                endcase
            end

            // Farm controller state machine
            case(frm_state)
                GREEN:  begin
                    if(long) begin
                        frm_state <= YELLOW;
                    end
                end
                YELLOW: begin
                    if(short) begin
                        frm_state <= RED;
                    end
                end
                RED:    begin
                    if(enable_frm) begin
                        frm_state <= GREEN;
                    end
                end
            endcase

            // Highway controller state machine
            case(hwy_state)
                GREEN:  begin
                    if(car_present && long) begin
                        hwy_state <= YELLOW;
                    end
                end
                YELLOW: begin
                    if(short) begin
                        hwy_state <= RED;
                    end
                end
                RED:    begin
                    if(enable_hwy) begin
                        hwy_state <= GREEN;
                    end
                end
            endcase

        endaction
    endmethod

    method farm_light();
        farm_light = frm_state;
    endmethod: farm_light
  
    method hwy_light();
        hwy_light = hwy_state ;
    endmethod: hwy_light

endmodule: mkDesign

endpackage: Design

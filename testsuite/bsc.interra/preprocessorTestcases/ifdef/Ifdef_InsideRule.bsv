package Design;

typedef enum {IDLE, REQUEST, ACQUISITION} HSstates
          deriving (Eq,Bits);  
 `define MAX 23

interface Design_IFC;
    method Bit#(1) req();
endinterface: Design_IFC

(*
       always_ready,
       always_enabled,
       clock_prefix = "clk",
       reset_prefix = "reset"
*)

module mkDesign (Design_IFC);

  Reg#(HSstates)    state();
  mkReg#(IDLE)      t_state(state);

  Reg#(Bit#(1))     req_reg();
  mkReg#(0)         t_req_reg(req_reg);
  
  rule fromIdle (state == IDLE);
    begin
`ifdef MAX
        req_reg   <= 1;
`else
       req_reg   <= 2;
`endif
`ifndef MAX
        state     <= REQUEST;
`else
        state     <=  ACQUISITION;
`endif
    end
  endrule

  method req();
     req = req_reg;
  endmethod: req

endmodule: mkDesign

endpackage: Design

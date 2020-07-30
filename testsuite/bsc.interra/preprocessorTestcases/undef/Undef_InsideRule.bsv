package Design;

typedef enum {IDLE, REQUEST, ACQUISITION} HSstates
          deriving (Eq,Bits);  

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
     `define MAX 23
     `undef MAX
`ifdef MAX
        req_reg   <= 1;
        state     <= REQUEST;
`else
       req_reg   <= 0;
        state     <= ACQUISITION;
`endif
    end
  endrule

  method req();
     req = req_reg;
  endmethod: req

endmodule: mkDesign

endpackage: Design

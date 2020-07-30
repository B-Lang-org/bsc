package Reg;

interface Reg_IFC;

method Action set_in (Bit#(1) a, Bit#(1) b);

method Bit#(1) out; 

endinterface: Reg_IFC

(*
    always_enabled,
    always_ready,
    CLK = "clk",
    RST_N = "reset"
*)

module mkReg(Reg_IFC);

Reg#(Bit#(1)) reg_a();
mkRegA#(0) reg_a_inst(reg_a);


method set_in (a,b);

action

//    reg_a <= a & b;
   reg_a = a & b;

endaction

endmethod

method out;

out = reg_a;

endmethod

endmodule: mkReg

endpackage: Reg

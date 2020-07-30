interface Bug446_1_IFC;

method Action set_in (Bit#(1) a);

method Bit#(1) out; 

endinterface: Bug446_1_IFC

(*
    synthesize,
    always_enabled,
    always_ready,
    CLK = "clk",
    RST_N = "reset"
*)

module mkBug446_1(Bug446_1_IFC);

Reg#(Bit#(1)) reg_a();
mkRegA#(0) reg_a(reg_a);

Reg#(Bit#(1)) a();
mkRegA#(0) a(a);

method set_in (a);

action

 Bit#(1) a = 1'b1;

 reg_a <= a ;

endaction

endmethod

method out;

  out = reg_a;

endmethod

endmodule: mkBug446_1

package Bug446_2;

interface Bug446_2_IFC;

method Action set_in (Bit#(1) a);

method Bit#(1) out; 

endinterface: Bug446_2_IFC

(*
    synthesize,
    always_enabled,
    always_ready,
    CLK = "clk",
    RST_N = "reset"
*)

module mkBug446_2(Bug446_2_IFC);

Reg#(Bit#(8)) reg_a();
mkRegU reg_a(reg_a);

Reg#(Bit#(8)) reg_a();
mkRegA#(8'h00) reg_a(reg_a);

Reg#(Bit#(8)) reg_a();
mkRegA#(8'hff) reg_a(reg_a);

Reg#(Bit#(1)) reg_a();
mkRegU reg_a(reg_a);

Reg#(Bit#(1)) reg_a();
mkRegA#(0) reg_a(reg_a);

Reg#(Bit#(1)) reg_a();
mkRegA#(1) reg_a(reg_a);

method set_in (a);

action

 reg_a <= a ;

endaction

endmethod

method out;

  out = reg_a;

endmethod

endmodule: mkBug446_2

endpackage: Bug446_2

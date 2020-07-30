import "BVI" DisplayReal =
module vDisplayReal#(real r)(Empty ifc);
   
   default_clock clk(CLK, (* unused *) CLK_GATE);
   default_reset no_reset;
   
   parameter val = r;
   
endmodule

(* synthesize *)
module mkRealPassThrough#(parameter Real r)();
   vDisplayReal(r);
endmodule

(* synthesize *)
module sysTwoLevelReal();
   mkRealPassThrough(99.17);
endmodule

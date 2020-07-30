import ValueImports::*;

(* synthesize *)
module mkTestInstParam ();
   Reg#(Bit#(32)) b <- mkReg(const_narrow);

   rule disp;
      $display(" b = %h", b);
      $finish(0);
   endrule
endmodule


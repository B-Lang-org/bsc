import Sub::*;

(* synthesize *)
module sysMethodConds_ActionArg_BVI ();
   Ifc s <- mkBVISub;

   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);

   rule r;
      if (c1)
         s.am1(0);
      else if (c2)
         s.am1(1);
   endrule
endmodule


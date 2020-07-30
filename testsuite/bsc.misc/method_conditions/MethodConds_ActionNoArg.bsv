import Sub::*;

(* synthesize *)
module sysMethodConds_ActionNoArg ();
   Ifc s <- mkUserSub;

   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);

   rule r;
      if (c1)
         s.am2();
      else if (c2)
         s.am2();
   endrule
endmodule


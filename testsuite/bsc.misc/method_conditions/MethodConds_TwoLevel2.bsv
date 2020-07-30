import Sub::*;

(* synthesize *)
module sysMethodConds_TwoLevel2();
   Ifc s <- mkMethodConds_TwoLevel2_Sub;

   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);

   rule r;
      if (c1)
         s.am1(0);
      else if (c2)
         s.am1(1);
   endrule
endmodule

module mkMethodConds_TwoLevel2_Sub(Ifc);
   Ifc u <- mkUserSub;

   method Action am1(Bit#(8) x);
      u.am1(x);
   endmethod

   method am2()   = noAction;
   method avm1(x) = actionvalue return(?); endactionvalue;
   method avm2()  = actionvalue return(?); endactionvalue;
   method vm1(x)  = ?;
   method vm2()   = ?;
endmodule

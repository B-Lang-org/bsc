import RegFile::*;
import Sub::*;

(* synthesize *)
module sysMethodConds_DroppedRule_Blocked();

   // State by which the two rules will conflict
   Reg#(UInt#(8)) rg <- mkReg(0);

   Ifc s1 <- mkUserSub;
   RegFile#(Bit#(4), Bool) rf <- mkRegFileFull;
   Reg#(Bool) c0 <- mkReg(True);

   // make this rule be the one that's blocked
   (* descending_urgency = "rblock, r1" *)
   rule r1;
      // conflict over shared resource
      rg <= rg + 1;

      if (c0)
         s1.am1(0);
      // Include a multiplicity resource (since the rule's resource is gone)
      else if (rf.sub(0))
         s1.am1(1);
   endrule

   rule rblock;
      // conflict over shared resource
      rg <= rg - 1;
   endrule

   Ifc s2 <- mkUserSub;
   Reg#(Bool) c1 <- mkReg(True);
   Reg#(Bool) c2 <- mkReg(True);

   // Have a second rule, to test that its CONDs are not removed
   rule r2;
      if (c1)
         s2.am1(0);
      else if (c2)
         s2.am1(1);
   endrule
endmodule


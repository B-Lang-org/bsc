import Vector::*;

(* synthesize *)
module sysMethodConds_VecSelAction_SamePos ();

   Reg#(UInt#(2)) idx <- mkReg(0);
   Vector#(4, Reg#(Bool)) rgs <- replicateM(mkReg(False));

   rule r1;
      rgs[idx] <= True;
   endrule

endmodule


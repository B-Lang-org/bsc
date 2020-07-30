import Vector::*;
import Sub::*;

(* synthesize *)
module sysMethodConds_VecSelCond();
   Ifc s <- mkUserSub;

   Vector#(3, Reg#(Bool)) cs <- replicateM(mkRegU);
   Reg#(Bit#(2)) idx <- mkReg(0);

   rule r;
      Bool c = cs[idx];
      if (c)
         s.am1(0);
   endrule
endmodule


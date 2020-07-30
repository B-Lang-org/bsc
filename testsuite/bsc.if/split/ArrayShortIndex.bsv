import Vector::*;

(* synthesize *)
module sysArrayShortIndex();
   Vector#(6, Reg#(Bool)) rgs <- replicateM(mkRegU);
   Reg#(Bit#(2)) idx <- mkReg(0);

   rule r;
      (* split *)
      rgs[idx] <= True;
      // an out-of-bounds rule would still do something
      idx <= idx + 1;
   endrule
endmodule

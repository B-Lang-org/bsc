import Vector::*;

(* synthesize *)
module sysArrayLongIndex();
   Vector#(6, Reg#(Bool)) rgs <- replicateM(mkRegU);
   Reg#(Bit#(3)) idx <- mkReg(0);

   rule r;
      (* split *)
      rgs[idx] <= True;
      // the out-of-bounds rule still does something
      idx <= idx + 1;
   endrule
endmodule

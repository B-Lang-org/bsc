import Vector::*;

typedef  Bit#(8)  T;

(* synthesize *)
module sysOneElemLargeIndex();

   Vector#(1, Reg#(T)) arr <- replicateM(mkRegU);

   Reg#(Bit#(4)) idx <- mkReg(0);

   rule doUpd;
      arr[idx] <= 17;
   endrule
endmodule


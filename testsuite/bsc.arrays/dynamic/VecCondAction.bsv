import Vector::*;
import FIFO::*;

(* synthesize *)
module sysVecCondAction();
   // the index can go out of bounds
   Vector#(3, Reg#(Bool)) rgs <- replicateM(mkRegU);
   Reg#(Bit#(2)) idx <- mkReg(0);

   // State with an Action with an implicit condition
   FIFO#(Bit#(8)) f <- mkFIFO;

   rule r;
      Bool c = rgs[idx];
      if (c)
         f.enq(0);
   endrule
endmodule


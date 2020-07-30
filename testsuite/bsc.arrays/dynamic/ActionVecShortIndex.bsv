import Vector::*;
import FIFO::*;

(* synthesize *)
module sysActionVecShortIndex();
   // the index cannot reach all of the elements
   Vector#(6, FIFO#(Bit#(8))) fs <- replicateM(mkFIFO);
   Reg#(Bit#(2)) idx <- mkReg(0);

   // tests:
   // (1) fs[4] and fs[5] should be unused
   //
   rule r;
      fs[idx].enq(0);
   endrule
endmodule


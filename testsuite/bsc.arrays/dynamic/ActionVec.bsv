import Vector::*;
import FIFO::*;

(* synthesize *)
module sysActionVec();
   // the index can go out of bounds
   Vector#(3, FIFO#(Bit#(8))) fs <- replicateM(mkFIFO);
   Reg#(Bit#(2)) idx <- mkReg(0);

   // tests:
   // (1) if the predicate is True when idx==3
   // (2) if the action is noAction (or fs[2]) when idx==3
   //
   rule r;
      fs[idx].enq(0);
   endrule
endmodule


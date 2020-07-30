import FIFO::*;
import Vector::*;

(* synthesize *)
module sysDynArraySelect2DMethodAction();

   Vector#(2, Vector#(2, FIFO#(Bool))) fs <- replicateM(replicateM(mkFIFO));

   Reg#(Bit#(1)) idx1 <- mkReg(0);
   Reg#(Bit#(1)) idx2 <- mkReg(0);

   let a = fs[idx1][idx2].enq(True);

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule

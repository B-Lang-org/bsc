import FIFO::*;
import Vector::*;

(* synthesize *)
module sysDynArraySelectMethodAction();

   Vector#(4, FIFO#(Bool)) fs <- replicateM(mkFIFO);

   Reg#(Bit#(2)) idx <- mkReg(0);

   let a = fs[idx].enq(True);

   rule r;
      $display("cond = %d", impCondOf(a));
   endrule

endmodule

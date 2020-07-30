import Vector ::*;
import FIFO   ::*;

typedef Bit#(8) T;

(* synthesize *)
module sysImpCond();

   Vector#(4, FIFO#(T)) fs <- replicateM(mkFIFO);
   Reg#(Bit#(2)) idx <- mkReg(0);

   // This should result in DynSel in the rule's condition,
   // when aggressive conditions is on
   rule r;
      fs[idx].enq(0);
   endrule

endmodule


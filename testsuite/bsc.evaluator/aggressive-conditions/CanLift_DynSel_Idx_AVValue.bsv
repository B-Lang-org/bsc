import FIFO::*;
import GetPut::*;
import Vector::*;

(* synthesize *)
module mkCanLift_DynSel_Idx_AVValue_Sub (Get#(Bit#(3)));
   method ActionValue#(Bit#(3)) get();
      return 0;
   endmethod
endmodule

(* synthesize *)
module sysCanLift_DynSel_Idx_AVValue ();

   Vector#(7, Reg#(Bool)) bs <- replicateM(mkRegU);

   Get#(Bit#(3)) g_idx <- mkCanLift_DynSel_Idx_AVValue_Sub;

   // ----
   // Test when the index is not liftable

   // modules with implicit conditions
   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   rule r1;
      let idx <- g_idx.get;
      Bool b = bs[idx];
      if (b)
         f1.enq(True);
      else
         f2.enq(True);
   endrule

   // ----
   // Test when the index is liftable

   Reg#(Bit#(2)) idx2 <- mkRegU;

   // modules with implicit conditions
   FIFO#(Bool) f3 <- mkFIFO;
   FIFO#(Bool) f4 <- mkFIFO;

   rule r2;
      Bool b = bs[idx2];
      if (b)
         f3.enq(True);
      else
         f4.enq(True);
   endrule

endmodule

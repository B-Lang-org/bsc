import FIFO::*;
import GetPut::*;
import Vector::*;

function Get#(Bool) dummyGet ();
   return (interface Get;
              method ActionValue#(Bool) get();
                 return True;
              endmethod
           endinterface);
endfunction

(* synthesize *)
module mkCanLift_DynSel_AVValue_Sub (Get#(Bool));
   return dummyGet;
endmodule

module mkRegGet (Get#(Bool));
   Reg#(Bool) rg <- mkRegU;

   method ActionValue#(Bool) get();
      return rg;
   endmethod
endmodule

(* synthesize *)
module sysCanLift_DynSel_AVValue ();

   Vector#(7, Get#(Bool)) gs <- replicateM(mkRegGet);

   gs[4] <- mkCanLift_DynSel_AVValue_Sub;

   // ----
   // Test when the AVValue is reachable

   Reg#(Bit#(3)) idx1 <- mkRegU;

   // modules with implicit conditions
   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   rule r1;
      Bool b <- gs[idx1].get;
      if (b)
         f1.enq(True);
      else
         f2.enq(True);
   endrule

   // ----
   // Test when the AVValue is not reachable

   Reg#(Bit#(2)) idx2 <- mkRegU;

   // modules with implicit conditions
   FIFO#(Bool) f3 <- mkFIFO;
   FIFO#(Bool) f4 <- mkFIFO;

   rule r2;
      Bool b <- gs[idx2].get;
      if (b)
         f3.enq(True);
      else
         f4.enq(True);
   endrule

endmodule

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
module mkCanLift_DynSel_2D_AVValue_Sub (Get#(Bool));
   return dummyGet;
endmodule

module mkRegGet (Get#(Bool));
   Reg#(Bool) rg <- mkRegU;

   method ActionValue#(Bool) get();
      return rg;
   endmethod
endmodule

(* synthesize *)
module sysCanLift_DynSel_2D_AVValue ();

   Vector#(3, Vector#(3, Get#(Bool))) gs <- replicateM(replicateM(mkRegGet));

   gs[1][2] <- mkCanLift_DynSel_2D_AVValue_Sub;

   // ----
   // Test when the AVValue is reachable

   Reg#(Bit#(2)) idx1 <- mkRegU;
   Reg#(Bit#(2)) idx2 <- mkRegU;

   // modules with implicit conditions
   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;

   rule r1;
      Bool b <- gs[idx1][idx2].get;
      if (b)
         f1.enq(True);
      else
         f2.enq(True);
   endrule

   // ----
   // Test when the AVValue is not reachable

   Reg#(Bit#(2)) idx3 <- mkRegU;
   Reg#(Bit#(1)) idx4 <- mkRegU;

   // modules with implicit conditions
   FIFO#(Bool) f3 <- mkFIFO;
   FIFO#(Bool) f4 <- mkFIFO;

   rule r2;
      Bool b <- gs[idx3][idx4].get;
      if (b)
         f3.enq(True);
      else
         f4.enq(True);
   endrule

endmodule

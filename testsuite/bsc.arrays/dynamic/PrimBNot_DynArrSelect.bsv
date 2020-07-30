import Vector::*;
import FIFO::*;

typedef Bit#(8)           Byte;
typedef Vector#(4, Byte)  Row;
typedef Vector#(4, Row)   Block;

(* synthesize *)
module mkTest();

   Vector#(2, FIFO#(Block)) bs <- replicateM(mkFIFO);
         Reg#(Bit#(1)) idx <- mkReg(0);

   Reg#(Vector#(4, Bit#(32))) dst <- mkRegU;

   rule r;
      // If PrimBNot isn't pushed inside the elements of a dynamic array
      // select, then the termination condition for this loop isn't optimized
      // and elaboration runs until the stack is exhausted.
      //
      dst <= map(pack, bs[idx].first);
   endrule

endmodule

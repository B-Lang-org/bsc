import Vector::*;
import FIFO::*;

typedef 256 Size;
Integer size = valueof(Size);

(* synthesize *)
module sysFIFOSelect(Empty);
   Vector#(Size, FIFO#(Bit#(17))) fifos <- replicateM(mkFIFO);
   
   Reg#(Bit#(17)) count <- mkReg(0);
   
   rule step(count < fromInteger(size));
      fifos[count].enq(count);
      count <= count + 1;
   endrule
   
   rule exit(count == fromInteger(size));
      for(Integer i = 0; i < size; i = i + 1)
	 $display("%0d", fifos[i].first);
      $finish(0);
   endrule
   
endmodule

   
   


import FIFO::*;

(* synthesize *)
(* options="-aggressive-conditions -no-inline-rwire -show-schedule" *)
module mkTest();

   FIFO#(Bool) f <- mkLFIFO;
   Reg#(Bool) p <- mkRegU();

   rule r;
      if (p) begin
	 f.enq(True);
	 // do something else so that the arms aren't the same
	 // (changing the argument to enq doesn't help, even making it int
	 // instead of Bool)
	 p <= True;
      end
      else begin
	 f.enq(True);
      end
   endrule

endmodule


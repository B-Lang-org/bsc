
import FIFO::*;

(* synthesize *)
(* options="-aggressive-conditions -no-inline-rwire -show-schedule" *)
module mkTest2();

   FIFO#(Bool) f <- mkLFIFO;
   Reg#(Bool) p <- mkRegU();

   rule r;

      if (p) begin
	 f.enq(True);
      end

      if(!p)
      begin
	 f.enq(True);
      end

   endrule

endmodule


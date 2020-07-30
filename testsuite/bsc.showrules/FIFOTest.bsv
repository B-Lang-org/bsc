import FIFOF::*;

(* synthesize *)
module mkFIFOTest();

   Reg#(UInt#(8)) count <- mkReg(0);
   FIFOF#(UInt#(8)) in1 <- mkFIFOF();
   FIFOF#(UInt#(8)) in2 <- mkFIFOF();
   FIFOF#(UInt#(8)) out <- mkFIFOF();

   rule sink;
      $display("out => %0d", out.first());
      out.deq();
   endrule

   rule merge;
      if (in1.first() < in2.first())
      begin
	out.enq(in1.first());
	in1.deq();
      end
      else
      begin
	out.enq(in2.first());
	in2.deq();
      end
   endrule

   rule gen_stimulus1(count % 4 != 2);
      $display("in1 <= %0d", count * 3);
      in1.enq(count * 3);
   endrule

   rule gen_stimulus2(count % 16 > 5);
      $display("in2 <= %0d", count * 2 + 9);
      in2.enq(count * 2 + 9);
   endrule

   rule incr;
      count <= count + 1;
   endrule

   rule done (count > 100);
      $finish(0);
   endrule

endmodule

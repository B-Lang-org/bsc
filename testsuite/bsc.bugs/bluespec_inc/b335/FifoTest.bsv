package FifoTest;

import FIFO::*;
import FIFOF::*;


(*
 synthesize
*)
module mkDesignI ();

  FIFO#(Bit#(8)) datafifo <- mkSizedFIFO(5) ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule dequeues ((counter > 13) && (counter < 35 )); action
     datafifo.deq ;
     Bit#(64) t <- $time();
     $display("%t -- dequeue %d", t, datafifo.first);
  endaction endrule

  rule data_write ((counter >= 1) && (counter < 25));  action
     datafifo.enq(counter);
     Bit#(64) t <- $time();
     $display("%t -- enqueue %d", t, counter);
  endaction endrule

  rule endofsim (counter > 40);
	$finish(0);
  endrule

endmodule



(*
 synthesize
*)
module mkDesignE ();

  FIFOF#(Bit#(8)) datafifo <- mkSizedFIFOF(5) ;
  Reg#(Bit#(8)) counter <- mkReg(0);
  Reg#(Bool) fail <- mkReg(False);

  rule always_fire (True);
	 counter <= counter + 1;
  endrule

  rule dequeues ((counter > 13) && (counter < 35 )); action
     datafifo.deq ;
     Bit#(64) t <- $time();
     $display("%t -- dequeue %d", t, datafifo.first);
  endaction endrule

  rule data_write ((counter >= 1) && (counter < 25));  action
     datafifo.enq(counter);
     Bit#(64) t <- $time();
     $display("%t -- enqueue %d", t, counter);
  endaction endrule

  rule endofsim (counter > 20);
	$finish(0);
  endrule

endmodule

endpackage: FifoTest

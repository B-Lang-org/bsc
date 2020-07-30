import BRAMFIFO::*;
import BRAM::*;
import StmtFSM::*;
import FIFO::*;
import FIFOF::*;

(* synthesize *)
module sysSizedBRAMFIFOTest();
   FIFOF#(Bit#(8)) dut <- mkSizedBRAMFIFOF(5);
   
   Stmt test =
   seq
      dut.enq(0);
      dut.enq(1);
      dut.enq(2);
      dut.enq(3);
      dut.enq(4);
      action
	 if (dut.notFull) $display("ERROR: Fifo should be full, but is not");
	 else noAction;
      endaction
      action
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.enq(6);
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.enq(7);
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.enq(8);
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.enq(9);
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      dut.enq(10);
      action
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      dut.enq(11);
      dut.enq(12);
      action
	 dut.enq(13);
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.enq(14);
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.enq(15);
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      action
	 dut.deq;
	 $display("%d", dut.first);
      endaction
      delay(10);
   endseq;
   
   mkAutoFSM(test);
endmodule

package WBTransmit;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Bank::*;
import Control::*;
import FIFO::*;
import StmtFSM::*;
import WBone::*;
import GetPut::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBTransmitIFC;
   interface Control        cntrl;
   interface WBoneOpTxRxIFC channel;
   interface WBoneOpTxRxIFC wb_channel;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkWBTransmit#(Integer id, BankClient_IFC bank) (WBTransmitIFC);
   
   FIFO#(WBoneOp) in_fifo  <- mkFIFO;
   FIFO#(WBoneOp) out_fifo  <- mkFIFO;
   
   FIFO#(WBoneOp) wb_in_fifo  <- mkFIFO;
   FIFO#(WBoneOp) wb_out_fifo <- mkFIFO1;
   
   Reg#(Bool) addr_acquired <- mkReg(False);
   Reg#(Bit#(16)) count <- mkReg(0);
   Reg#(Bit#(16)) i <- mkReg(0);
   Reg#(Bit#(16)) addr <- mkReg(0);
   
   Reg#(Bool) wbone_waiting <- mkReg(False);

   Stmt transmit_seq =
   seq
      while (True)
	 seq
	    addr_acquired <= False;
	    while (!addr_acquired)
	       action
		  let wboneop = in_fifo.first;
		  addr <= truncate(wboneop.addr.data);
		  let acquired <- bank.withdraw(truncate(wboneop.addr.data));
		  addr_acquired <= acquired;
//		  $display("(%5d) transmit first word", $time);
//		  displayWBoneOp(wboneop);
	       endaction
	    action
	       $display("(%5d) (Port %0d) withdrawing address %0d", $time, addr, id );
	       let wboneop = in_fifo.first;
	       let data = wboneop.data.data;
	       let rest =  data[15: 0];
	       count <= data[31:16];
	       wb_out_fifo.enq(wboneop);
	       in_fifo.deq;
	    endaction
	    action
	       // Get wb acknowledgement.
	       let value = wb_in_fifo.first();
	       wb_in_fifo.deq();
	       if (value.status != ACK) $display("Error Non-ACK detected.");
	    endaction
	    for (i <= 0; i < count; i <= i + 4)
	       seq
		  action
		     let wboneop = in_fifo.first;
		     wb_out_fifo.enq(wboneop);
		     in_fifo.deq;
		  endaction
		  action
		     // Get wb acknowledgement.
		     let value = wb_in_fifo.first();
		     wb_in_fifo.deq();
		     if (value.status != ACK) $display("Error Non-ACK detected.");
		  endaction
	       endseq
//	    $display("(%5d) (Port %0d) pre deposit", $time, id);
	    action
	       $display("(%5d) (Port %0d) depositing address %0d", $time, addr, id );
	       bank.deposit(truncate(addr));
	    endaction
	 endseq
   endseq;
   
   let transmit_fsm <- mkFSM(transmit_seq);
   
   interface Control cntrl;
      method Action init();
	 transmit_fsm.start();
      endmethod
   endinterface
   
   interface WBoneOpTxRxIFC channel;
      interface Get tx = fifoToGet(out_fifo);
      interface Put rx = fifoToPut(in_fifo);
   endinterface
   
   interface WBoneOpTxRxIFC wb_channel;
      interface Get tx;
	 method ActionValue#(WBoneOp) get if (!wbone_waiting);
	    let value = wb_out_fifo.first();
	    wb_out_fifo.deq();
	    wbone_waiting <= True;
            return value;
	 endmethod
      endinterface
      interface Put rx;
	 method Action put (x) if (wbone_waiting);
	    wb_in_fifo.enq(x);
	    wbone_waiting <= False;
	 endmethod
      endinterface
   endinterface
   
endmodule

endpackage
package WBAssemble;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import WBone::*;
import GetPut::*;
import FIFO::*;
import Control::*;
import StmtFSM::*;
import EthFrame::*;
import Util::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBAssembleIFC;
   interface Control cntrl;
   interface WBoneOpTxRxIFC  wb_channel;
   interface Get#(Frame)     tx;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkWBAssemble#(Integer address) (WBAssembleIFC);

   FIFO#(WBoneOp) wb_in_fifo  <- mkFIFO;
   FIFO#(WBoneOp) wb_out_fifo <- mkFIFO;
   
   FIFO#(Frame) frame_fifo <- mkFIFO;
   
   Reg#(Bit#(16)) receive_size <- mkReg(0);
   Reg#(Bit#(16)) rest <- mkReg(0);
   
   Reg#(Frame) rx_reg <- mkRegU;
   Reg#(Bit#(SizeOf#(Frame))) rx_bit_reg <- mkReg(0);
   
   Reg#(Bit#(32)) count_rx  <- mkReg(0);
   Reg#(Bit#(16)) i  <- mkReg(0);
   
   Stmt assemble_seq =
   seq
      while (True)
	 seq
	    action
	       let wboneop = wb_in_fifo.first();
	       wb_in_fifo.deq();
	       wboneop.status = ACK;
	       wb_out_fifo.enq(wboneop);
	    
	       let data = wboneop.data.data;
               receive_size <= data[31:16];
               rest <= data[15: 0];
//	       $display("(%5d) slave receives wbone_op %h", $time, data[15: 0]); 
//	       displayWBoneOp(wboneop);
	       rx_bit_reg <= 0;
	    endaction
	    if (rest != 16'hDDDD)
	       seq
		  $display("(%5d) something is messed up!!!", $time);
		  continue;
	       endseq
	    count_rx <= 0;
	    for (i <= 0; i < receive_size; i <= i + 4)
	       action
		  let wboneop = wb_in_fifo.first();
		  wb_in_fifo.deq();
		  wboneop.status = ACK;
		  wb_out_fifo.enq(wboneop);
		  
		  Bit#(32) word = truncate(wboneop.data.data);
		  rx_bit_reg <= truncate({rx_bit_reg, word});
		  count_rx <= count_rx + 32;
	       endaction
	    action
	       let size_rx = fromInteger(getSizeOf(rx_bit_reg));
	       Nat delta = size_rx - count_rx;
	       rx_bit_reg <= truncate(rx_bit_reg << delta);
	    endaction
	    action
	       $display("(%5d) Port (%0d) .... Frame Assembled !!!!!!!!!!!!!!!!!.", $time, address);
	       let frame = remove_trailing_data(unpack(rx_bit_reg));
	       frame_fifo.enq(frame);
	       displayFrame(frame);
	    endaction
	 endseq
   endseq;
   
   let assemble_fsm <- mkFSM(assemble_seq);

   interface Control cntrl;
      method Action init();
	 assemble_fsm.start;
      endmethod
   endinterface

   interface WBoneOpTxRxIFC wb_channel;
      interface Get tx;
	 method ActionValue#(WBoneOp) get;
	    let value = wb_out_fifo.first();
	    wb_out_fifo.deq();
            return value;
	 endmethod
      endinterface
      interface Put rx;
	 method Action put (x);
	    wb_in_fifo.enq(x);
	 endmethod
      endinterface
   endinterface
   
   interface Get tx =fifoToGet(frame_fifo);
   
endmodule

      
endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

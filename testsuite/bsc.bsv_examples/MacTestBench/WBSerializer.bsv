package WBSerializer;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Control::*;
import EthFrame::*;
import FIFO::*;
import GetPut::*;
import Randomizeable::*;
import StmtFSM::*;
import Util::*;
import WBone::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface WBSerializerIFC;
   interface Control        cntrl;
   interface Put#(Frame)    rx;
   interface Get#(WBoneOp)  tx;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkWBSerializer#(Integer id, function Bit#(32) get_addr(Frame frame)) (WBSerializerIFC);
   
   Randomize#(WBoneOp) wboneop_gen <- mkRandomizer;
   
   FIFO#(Frame)   frame_in_fifo <- mkFIFO;
   FIFO#(WBoneOp) wb_out_fifo   <- mkFIFO;
   
   Reg#(Frame) tx_reg <- mkRegU;
   Reg#(Bit#(SizeOf#(Frame))) tx_bit_reg <- mkReg(0);
   
   Reg#(Bit#(32)) wb_addr <- mkReg(0);
   Reg#(Bit#(16))  i       <- mkReg(0);
   
   Stmt serialize_seq =
   seq
      while (True)
	 seq
	    action
	       let frame = frame_in_fifo.first();
	       tx_reg <= frame;
	       tx_bit_reg <= pack(frame);
//	       $display("(%5d) Into Words (dest %d)", $time, calculateDestinationPort(frame));
	       $display("(%5d) (Port %0d) serializing", $time, id);
	       displayFrame(frame);
	       
	       Bit#(32) data;
               data[31:16] = getFrameByteSize(frame);
               data[15: 0] = 16'hDDDD;
	       
	       Bit#(32) addr = get_addr(frame);
	       wb_addr <= addr;

	       let wboneop <- wboneop_gen.next();
	       wboneop.kind = WRITE;
	       wboneop.addr = BusAddr { data: {0, addr}, tag: unpack(0) };
	       wboneop.data = BusData { data: {0, data}  , tag: unpack(0) };
	       wboneop.sel = unpack({0,4'hF});
//	       $display("(%5d) descriptor", $time);
//	       displayWBoneOp(wboneop);
	       wb_out_fifo.enq(wboneop);
	    endaction
	    for (i <= 0; i < truncate(getFrameByteSize(tx_reg)); i <= i + 4)
	       action
		  Bit#(32) word = grab_left(tx_bit_reg);
		  tx_bit_reg <= truncate(tx_bit_reg << 32);
		  
		  let wboneop <- wboneop_gen.next();
		  wboneop.kind = WRITE;
		  wboneop.addr = BusAddr { data: {0, wb_addr}, tag: unpack(0) };
		  wboneop.data = BusData { data: {0, word}  , tag: unpack(0) };
		  wboneop.sel = unpack({0,4'hF});
//		  $display("(%5d) sending word %d %h", $time, i, word);
//		  displayWBoneOp(wboneop);
		  wb_out_fifo.enq(wboneop);
	       endaction
	    frame_in_fifo.deq;
	 endseq
   endseq;

   let serialize_fsm <- mkFSM(serialize_seq);

   interface Control cntrl;
      method Action init();
	 wboneop_gen.cntrl.init;
	 serialize_fsm.start;
      endmethod
   endinterface
   
   interface Put rx = fifoToPut(frame_in_fifo);

   interface Get tx = fifoToGet(wb_out_fifo);

endmodule


endpackage
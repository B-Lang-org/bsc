package SWEmulator;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Util::*;
import FIFO::*;
import GetPut::*;
import EthFrame::*;
import Randomizeable::*;
import WBone::*;
import WBMaster::*;
import SimpleRam::*;
import WBRam::*;
import TbEnvConfigs::*;
import TxRxPntArray::*;
import StmtFSM::*;
import Control::*;
import Scoreboard::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface SWEmulatorIFC;
   interface Control        cntrl;
   method Action int_in (Bool value);
   interface FrameTxRxIFC   frame_channel;
   interface WBoneOpTxRxIFC wb_channel;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkSWEmulator#(TbEnvConfigs parent, 
		     WBRamIFC ram, 
		     TxRxPntArrayRamIFC txrx_pnt_map,
		     Scoreboard scoreboard) (SWEmulatorIFC);

   Reg#(Bool) initialized <- mkReg(False);
   Reg#(Bool) wbone_waiting <- mkReg(False);

   FIFO#(Frame)   frame_in_fifo  <- mkFIFO;
   FIFO#(Frame)   frame_out_fifo <- mkFIFO;
   FIFO#(WBoneOp) wb_in_fifo     <- mkFIFO;
   FIFO#(WBoneOp) wb_out_fifo    <- mkFIFO1;

   FIFO#(Bit#(32)) avail_txbd <- mkSizedFIFO(256);
   FIFO#(Bit#(32)) busy_txbd <- mkSizedFIFO(256);

   Reg#(Bit#(8))  i       <- mkReg(0);
   Reg#(Bit#(8))  j       <- mkReg(0);
   Reg#(Bit#(8))  k       <- mkReg(0);
   Reg#(Bit#(32)) bd_addr <- mkReg(0);

   Reg#(Frame) tx_reg <- mkRegU;
   Reg#(Bit#(SizeOf#(Frame))) tx_bit_reg <- mkReg(0);

   Reg#(Frame) rx_reg <- mkRegU;
   Reg#(Bit#(SizeOf#(Frame))) rx_bit_reg <- mkReg(0);

   Reg#(Bool) interrupt <- mkReg(False);
   Reg#(Bool) received <- mkReg(False);
   Reg#(Bool) transmitted <- mkReg(False);
   
   Randomize#(WBoneOp) wboneop_gen <- mkRandomizer;

   Reg#(Bit#(32)) next_rxbd <- mkReg(?);
   Reg#(Bit#(32)) txbd <- mkReg(?);

   Reg#(Bit#(16)) receive_size <- mkReg(?);

   Reg#(Bit#(32)) count_rx  <- mkReg(0);

   Stmt init_seq =  
   seq
      action
	 $display("Starting SWEM init sequence.");
	 bd_addr <=  32'h0000_0400;
      endaction
      for (i <= parent.n_tx_bd; i > 0; i <= i-1)
	 action
	    avail_txbd.enq(bd_addr);
	    bd_addr <= bd_addr + 8;
	 endaction
      // Push a "wrap" flag
      avail_txbd.enq(32'hFFFF_FFFF);
      action
	 initialized <= True;
	 $display("SWEM init sequence complete.");
      endaction
   endseq;

   
   Stmt tx_driver_seq =
   seq
      while (!initialized) noAction;
      while (True)
	 seq
	    action
	       let frame = frame_in_fifo.first();
	       let bd_addr = avail_txbd.first();
	       let size = getFrameByteSize(frame);
	       
	       Bit#(32) tx_pnt = txrx_pnt_map.read(bd_addr);

	       tx_reg <= frame;
	       tx_bit_reg <= pack(frame);
	       $display("Into SWEM bd_addr = %0h, tx_pnt = %0h (%5d)", bd_addr, tx_pnt, $time);
	       displayFrame(frame);
	       scoreboard.sent_from_mac_side(frame);
	    endaction
	    for (j <= 0; j < truncate(getFrameByteSize(tx_reg)); j <= j + 4)
	       action

		  let bd_addr = avail_txbd.first();

		  Bit#(32) tx_pnt = txrx_pnt_map.read(bd_addr);
		  Bit#(32) word = grab_left(tx_bit_reg);
		  tx_bit_reg <= truncate(tx_bit_reg << 32);
		  ram.write(tx_pnt + {0, j}, word);
	       endaction
	    action
	       let bd_addr = avail_txbd.first;
	       txbd <= bd_addr;
	       avail_txbd.deq;
	       busy_txbd.enq(bd_addr);
	    endaction
	    action
	       let frame = frame_in_fifo.first();
	       frame_in_fifo.deq();
	       
	       let bd_addr = txbd;
	       let wrap = 0;
	       
	       if (avail_txbd.first == 32'hFFFF_FFFF)
		  begin
		     avail_txbd.deq;
		     busy_txbd.enq(32'hFFFF_FFFF);
		     wrap = 1;
		  end

	       Bit#(32) data;
	       
               data[31:16] = getFrameByteSize(frame);
               data[15: 0] = 16'hD400;
	       data[13] = wrap;

	       let wboneop <- wboneop_gen.next();
	       wboneop.kind = WRITE;
	       wboneop.addr = BusAddr { data: {0, bd_addr}, tag: unpack(0) };
	       wboneop.data = BusData { data: {0, data}  , tag: unpack(0) };
	       wboneop.sel = unpack({0,4'hF});
	       wb_out_fifo.enq(wboneop);
	    endaction
	    action
	       let value = wb_in_fifo.first();
	       wb_in_fifo.deq();
	       if (value.status != ACK) $display("Error Non-ACK detected.");
	    endaction
	 endseq
      
   endseq;

   Stmt int_server_seq =
   seq
      next_rxbd <= parent.bd_offset + ({0, parent.rx_bd_offset} * 8);
      while (True)
	 seq
	    action
	       received <= False;
	       rx_bit_reg <= 0;
	    endaction
	    await(interrupt);
	    action
	       $display("(%5d) Interrupt!", $time);
	    endaction
	    action
	       $display("Doing interrupt READ");
	       let bd_addr = 32'h4;
	       let wboneop <- wboneop_gen.next();
	       wboneop.kind = READ;
	       wboneop.addr = BusAddr { data: {0, bd_addr}, tag: unpack(0) };
	       wboneop.data = unpack(0);
	       wboneop.sel = unpack({0,4'hF});
	       wb_out_fifo.enq(wboneop);
	    endaction
	    action
	       let wboneop = wb_in_fifo.first();
	       wb_in_fifo.deq();
	       if (wboneop.status != ACK) $display("Error  Non-ACK detected.");

	       let value = wboneop.data.data;
//	       $display("Interrupt value %h", value);
	       
	       received <= (value[2] == 'b1) || (value[3] == 'b1);
	       transmitted <= (value[0] == 'b1) || (value[1] == 'b1);

	       // Write it back to clear the interrupt
	       wboneop.kind = WRITE;
	       wb_out_fifo.enq(wboneop);
	    endaction
	    action
	       // Get the writeback acknowledgement.
	       let value = wb_in_fifo.first();
	       wb_in_fifo.deq();
	       if (value.status != ACK) $display("Error Non-ACK detected.");
	    endaction
	    if (received)
	       while (True)
		  seq
		     action
			let bd_addr = next_rxbd;
			let wboneop <- wboneop_gen.next();
			wboneop.kind = READ;
			wboneop.addr = BusAddr { data: {0, bd_addr}, tag: unpack(0) };
			wboneop.data = unpack(0);
			wboneop.sel = unpack({0,4'hF});
			wb_out_fifo.enq(wboneop);
		     endaction
		     action
			let wboneop = wb_in_fifo.first();
			if (wboneop.status != ACK) $display("Error Non-ACK detected.");

			let value = wboneop.data.data;
			let length = value[31:16];

			receive_size <= length;
			
			if (value[15] == 1) $display("Empty !!!!");
			Bit#(32) rx_pnt = txrx_pnt_map.read(next_rxbd);
//			$display("RxBd addr: %h, length: %d, value %h, rx_pnt: %h", next_rxbd, length, value, rx_pnt);
			count_rx <= 0;
		     endaction
		     for (k <= 0; k < truncate(receive_size); k <= k + 4)
			action
			   Bit#(32) rx_pnt = txrx_pnt_map.read(next_rxbd);
			   let word = ram.read(rx_pnt + {0, k});
			   rx_bit_reg <= truncate({rx_bit_reg, word});
			   count_rx <= count_rx + 32;
			endaction
		     action
			let size_rx = fromInteger(getSizeOf(rx_bit_reg));
			Nat delta = size_rx - count_rx;
			rx_bit_reg <= truncate(rx_bit_reg << delta);
		     endaction
		     action
			let wboneop = wb_in_fifo.first();
			wb_in_fifo.deq();
			let value = wboneop.data.data;
			let tag = wboneop.data.tag;
			if (value[13] == 1)
			   next_rxbd <= parent.bd_offset + ({0, parent.rx_bd_offset} * 8);
			else
			   next_rxbd <= next_rxbd + 8;
			wboneop.kind = WRITE;
			value[15] = 1; // mark as empty.
			wboneop.data = BusData { data: value  , tag: tag };
			wb_out_fifo.enq(wboneop);
			if (False && (value[0] == 1))
			   begin
			      $display("(%5d) Receive test frame encountered late collision, discarding.", $time);
			      let frame = remove_trailing_data(unpack(rx_bit_reg));
			      displayFrame(frame);
			   end
			else if (value[1] == 1)
			   begin
			      $display("(%5d) Receive test frame includes CRC error, discarding.", $time);
			      let frame = remove_trailing_data(unpack(rx_bit_reg));
			      displayFrame(frame);
			   end
			else
			   begin
			      $display("(%5d) Receive test frame assembled,", $time);
			      let frame = remove_trailing_data(unpack(rx_bit_reg));
			      displayFrame(frame);
			      frame_out_fifo.enq(frame);
			   end
		     endaction
		     action
			let value = wb_in_fifo.first();
			wb_in_fifo.deq();
			if (value.status != ACK) $display("Error Non-ACK detected.");
		     endaction
		     break;
		  endseq
	    if (transmitted)
	       seq
		  action
		     let bd_addr = busy_txbd.first;
		     busy_txbd.deq;
		     avail_txbd.enq(bd_addr);
		     let wboneop <- wboneop_gen.next();
		     wboneop.kind = READ;
		     wboneop.addr = BusAddr { data: {0, bd_addr}, tag: unpack(0) };
		     wboneop.data = unpack(0);
		     wboneop.sel = unpack({0,4'hF});
		     wb_out_fifo.enq(wboneop);
		  endaction
		  action
		     let bd_addr = busy_txbd.first;
		     if (bd_addr == 32'hFFFF_FFFF)
			begin
			   busy_txbd.deq;
		           avail_txbd.enq(bd_addr);
			end
		     let wboneop = wb_in_fifo.first();
		     wb_in_fifo.deq();
		     if (wboneop.status != ACK) $display("Error Non-ACK detected.");
		  endaction
	       endseq
	    await(!interrupt);
	 endseq
   endseq;

   let init_fsm <- mkFSM(init_seq);
   let tx_driver_fsm <- mkFSM(tx_driver_seq);
   let int_server_fsm <- mkFSM(int_server_seq);

   interface Control cntrl;
      method Action init();
	 init_fsm.start();
	 tx_driver_fsm.start();
	 int_server_fsm.start();
	 wboneop_gen.cntrl.init();
      endmethod
   endinterface

   method Action int_in (Bool value);
      interrupt <= value;
   endmethod

   interface FrameTxRxIFC frame_channel;
      interface Get tx = fifoToGet(frame_out_fifo);
      interface Put rx = fifoToPut(frame_in_fifo);
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

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////


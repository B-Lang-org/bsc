package MiiPhyLayer;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import BGetPut::*;
import Control::*;
import Crc::*;
import EthFrame::*;
import FIFO::*;
import FIFOF::*;
import GetPut::*;
import Mii::*;
import Randomizeable::*;
import StmtFSM::*;
import TbEnvConfigs::*;
import Util::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface MiiPhyLayerIFC;
   interface Control cntrl;
   interface FrameTxBRxIFC    frame_channel;
   interface MiiNibbleTxRxIFC mii_nibble_channel;
   interface IndicationsIFC indications;      
endinterface

interface MiiPhyLayerTxIFC;
   interface Control cntrl;
   interface Get#(MiiNibble) tx;
   interface BPut#(Frame) rx;
   interface MediaIFC media;
   method Bool waiting_to_tx;
endinterface

interface MiiPhyLayerRxIFC;
   interface Control cntrl;
   interface Put#(MiiNibble) rx;
   interface Get#(Frame) tx;
   interface MediaIFC media;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module mkMiiPhyLayer#(Bool full_duplex) (MiiPhyLayerIFC);
   
   MiiPhyLayerRxIFC mii_rx <- mkMiiPhyLayerRx(full_duplex);
   MiiPhyLayerTxIFC mii_tx <- mkMiiPhyLayerTx(full_duplex);
   Wire#(Bool) collision <- mkWire;
   
   Randomize#(Collision) collision_gen <- mkRandomizer;
   Reg#(Bit#(16)) collision_symbol <- mkReg(0);
   Reg#(Bit#(16)) count <- mkReg(0);
   
   Reg#(Bool) force_collision <- mkReg(False);
   
   Reg#(Bool) crs_rx_force <- mkReg(False);
   Reg#(Bool) crs_rx_supress <- mkReg(False);
   
   rule collision_update;
      collision <= mii_rx.media.carrier_out && mii_tx.media.carrier_out && !full_duplex;
   endrule
   
   rule collision_announce (collision);
      $display("(%5d) Collision!", $time);
   endrule
   
   rule carrier_connect;
      let crs_rx = (mii_rx.media.carrier_out || crs_rx_force) && !crs_rx_supress;
      mii_rx.media.carrier_in(mii_tx.media.carrier_out);
      mii_tx.media.carrier_in(crs_rx);
   endrule
   
   Stmt collision_seq =
   seq
      while (True)
	 seq
	    action
	       let collision <- collision_gen.next();
	       let add_collisions <- $test$plusargs("add_collisions");
	       let receive <- $test$plusargs("receive");
	       let transmit <- $test$plusargs("transmit");
	       collision_symbol <=  
	         (add_collisions && receive && transmit) ? collision.on_symbol : 0;
	       crs_rx_supress <= False;
	       crs_rx_force <= False;
	       count <= 0;
	    endaction
	    // wait until tx is idle and rx is active
	    await(mii_rx.media.carrier_out && !mii_tx.media.carrier_out); 
	    if (full_duplex || (collision_symbol == 0))
	       await(!mii_rx.media.carrier_out);
	    else
	       seq
		  crs_rx_force <= True;
		  // wait until rx is idle and tx is ready to go.
		  await(!mii_rx.media.carrier_out && mii_tx.waiting_to_tx); 
		  // wait for rx to go active again.
		  await(mii_rx.media.carrier_out); 
		  // extra 13 accounts for preamble delay
		  while ((count < (collision_symbol + 13)) && mii_rx.media.carrier_out) 
		     count <= count + 1;
		  if (mii_rx.media.carrier_out)
		     action
			crs_rx_supress <= True;
			crs_rx_force <= False;
			$display("(%5d) Forcing a collision on symbol #%0d...", $time, collision_symbol);
		     endaction
	       endseq
	 endseq
   endseq;
   
   let collision_fsm  <- mkFSM(collision_seq);

   interface Control cntrl;
      method Action init();
	 collision_gen.cntrl.init;
	 collision_fsm.start;
	 mii_rx.cntrl.init;
	 mii_tx.cntrl.init;
      endmethod
   endinterface
   
   interface FrameTxBRxIFC frame_channel;
      interface Get tx = mii_rx.tx;
      interface BPut rx = mii_tx.rx;
   endinterface
   
   interface MiiNibbleTxRxIFC mii_nibble_channel;
      interface Get tx =  mii_tx.tx;
      interface Put rx = mii_rx.rx;
   endinterface
   
    interface IndicationsIFC indications;
       method Indications indicate();
	  let collision = mii_rx.media.carrier_out && mii_tx.media.carrier_out && !full_duplex;
	  let carrier = mii_rx.media.carrier_out || mii_tx.media.carrier_out;
	  return Indications {collision: collision,
			      carrier: carrier
			      };
       endmethod
   endinterface
   
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module mkMiiPhyLayerTx#(Bool full_duplex) (MiiPhyLayerTxIFC);
   
   FIFOF#(Frame)    in_fifo  <- mkFIFOF1;
   FIFO#(MiiNibble) mii_out_fifo <- mkFIFO;

   Reg#(Bool) crs_out <- mkReg(False);
   Reg#(Bool) crs_in <- mkReg(False);
   Wire#(Bool) collision <- mkWire;
   
   Reg#(Bool) waiting <- mkReg(False);
   
   Reg#(Bit#(32)) count_tx  <- mkReg(0);
   Reg#(Bit#(32)) size_tx  <- mkReg(0);

   Reg#(Bit#(SizeOf#(Frame))) tx_bit_reg <- mkReg(0);

   CrcCalculatorIFC crc_tx <- mkCrcCalculator;
   
   rule collision_update;
      collision <= crs_in && crs_out && !full_duplex;
   endrule

   Stmt tx_driver_seq =
   seq
      while (True)
	 seq
	    action
	       let frame = in_fifo.first();
	       $display("(instance %m): Transmitting frame enters phy ... (%5d).", $time);
	       displayFrame(frame);
	       tx_bit_reg <= pack(frame);
	       waiting <= True;
	    endaction
	    await(!crs_in || full_duplex);
	    action
	       let frame = in_fifo.first();
	       let max = fromInteger(valueOf(MaxDataLength));
	       size_tx <= {0, getFrameByteSize(frame)} * 8;
	       count_tx <= 0;
	       crc_tx.initialize();
	       crs_out <= True;
	       waiting <= False;
	    endaction
	    repeat (15)
	       seq
		  action
		     let nibble = 4'b0101;
		     mii_out_fifo.enq(MiiNibble { nibble: nibble, err: False});
		  endaction
	       endseq
	    action
	       let nibble = 4'b1101;
	       mii_out_fifo.enq(MiiNibble { nibble: nibble, err: False});
	    endaction
	    while ((count_tx < (size_tx + 32)) && !collision)
	       action
		  if (count_tx < size_tx)
		     begin
			let value = tx_bit_reg;
			Bit#(4) nibble;
			Bit#(8) two_nibbles = grab_left(value);
			if (count_tx[2] == 0)
			   begin
			      nibble = two_nibbles[3:0];
			   end
			else
			   begin
			      nibble = two_nibbles[7:4];
			      tx_bit_reg <= value << 8;
			   end
			crc_tx.data.put(Valid(nibble));
			mii_out_fifo.enq(MiiNibble { nibble: nibble, err: False});
		     end
		  else
		     begin // send 8 nibbles of crc.
			crc_tx.data.put(Nothing);
			let nibble = crc_tx.getFcs();
			mii_out_fifo.enq(MiiNibble { nibble: nibble, err: False});
		     end
		  count_tx <= count_tx + 4;
	       endaction
	    if (collision)
	       repeat (8)
	          seq
		     action
			let nibble = 4'b1001;
			mii_out_fifo.enq(MiiNibble { nibble: nibble, err: True});
		     endaction
		  endseq
	    else
	       $display("(%5d) Finished, no collision", $time);
	    in_fifo.deq();
	    crs_out <= False;
	 endseq
   endseq;
  
   let tx_driver_fsm  <- mkFSM(tx_driver_seq);
   
   interface Control cntrl;
      method Action init();
	 tx_driver_fsm.start();
      endmethod
   endinterface
   
   interface Get tx;
      method ActionValue#(MiiNibble) get ();
	 let value = mii_out_fifo.first;
	 mii_out_fifo.deq;
	 return value;
      endmethod
   endinterface
   
   interface BPut rx = fifofToBPut(in_fifo);
   
   interface MediaIFC media;
      method Bool carrier_out();
	 return crs_out;
      endmethod
      method Action carrier_in (Bool value);
	 crs_in <= value;
      endmethod
   endinterface
      
   method Bool waiting_to_tx();
      return waiting;
   endmethod

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module mkMiiPhyLayerRx#(Bool full_duplex) (MiiPhyLayerRxIFC);
      
   FIFO#(Frame)        out_fifo     <-  mkFIFO1;
   FIFOF#(MiiNibble)   mii_in_fifo  <-  mkSizedFIFOF(8); // make this big enough to suck up 
                                                         // any extra cycles in the rx_monitor_fsm;
   Reg#(Bool) crs_out <- mkReg(False);
   Reg#(Bool) crs_in <- mkReg(False);
   
   Reg#(Bit#(32)) count_rx  <- mkReg(0);
   Reg#(Bit#(32)) size_rx  <- mkReg(0);

   Reg#(Bit#(SizeOf#(Frame))) rx_bit_reg <- mkReg(0);

   Reg#(Bool) done <- mkReg(?);

   CrcCalculatorIFC crc_rx <- mkCrcCalculator;

   Stmt rx_monitor_seq =
   seq
      while (True)
	 seq
	    action
	       crs_out <= False;
	       count_rx <= 0;
	       mii_in_fifo.clear();
	       crc_rx.initialize();
	    endaction
	    while (!(mii_in_fifo.notEmpty() && (mii_in_fifo.first.nibble == 4'b0101)))
	       action
		  if (mii_in_fifo.notEmpty()) mii_in_fifo.deq();
	       endaction
	    while (mii_in_fifo.notEmpty() && (mii_in_fifo.first.nibble == 4'b0101))
	       action
		  crs_out <= True;
		  count_rx <= count_rx + 1;
		  mii_in_fifo.deq();
	       endaction
	    if (count_rx < 5)
	       continue;
	    else
	       action
		  $display("(instance %m): Found Preamble (length = %d) ... (%5d)", count_rx, $time);
		  done <= False;
	       endaction
	    while (mii_in_fifo.notEmpty() && !done)
	       action
		  let value = mii_in_fifo.first();
		  $display("Should be d: %h ... (%5d)", value.nibble, $time);
		  mii_in_fifo.deq();
		  rx_bit_reg <= 0;
		  count_rx <= 0;
		  size_rx <= fromInteger(getSizeOf(rx_bit_reg));
		  done <= True;
	       endaction
	    while (mii_in_fifo.notEmpty())
	       action
		  let value = mii_in_fifo.first();
		  crc_rx.data.put(Valid(value.nibble));
		  if (count_rx[2] == 0)
		     begin
			rx_bit_reg <= truncate({rx_bit_reg, value.nibble});
		     end
		  else
		     begin
			let frame_value = rx_bit_reg >> 4;
			Bit#(4) nibble = truncate(rx_bit_reg);
			rx_bit_reg <= truncate({frame_value, value.nibble, nibble});
		     end
		  count_rx <= count_rx + 4;
		  mii_in_fifo.deq();
	       endaction
	    rx_bit_reg <= truncate(rx_bit_reg << (size_rx - count_rx));
	    action
	       $display("(instance %m): Transmit test frame assembled ... %d %d %d (%5d).", 
		  size_rx, count_rx, (size_rx - count_rx), $time);
	       let frame = remove_trailing_data(unpack(rx_bit_reg));
	       let size = getFrameByteSize(frame);
	       Bit#(32) fcs = grab_left(rx_bit_reg << (size * 8));
//	       $display("FCS: %h", fcs);
	       if (crc_rx.getCrc() != 32'hc704dd7b)  // CRC not equal to magic number
		  begin
		     $display("Error: CRC value is not correct!!!, discarding");
		     displayFrame(frame);
		  end
	       else
		  begin
		     $display("Notice: CRC value is correct!!!");
		     displayFrame(frame);
		     out_fifo.enq(frame);
		  end
	    endaction
	 endseq
   endseq;

   let rx_monitor_fsm <- mkFSM(rx_monitor_seq);

   interface Control cntrl;
      method Action init();
	 rx_monitor_fsm.start();
      endmethod
   endinterface
   
   interface Put rx;
      method Action put (x);
	 mii_in_fifo.enq (x);
      endmethod
   endinterface
   interface Get tx = fifoToGet(out_fifo);
      
      
   interface MediaIFC media;
      method Bool carrier_out();
	 return crs_out;
      endmethod
      method Action carrier_in(Bool value);
	 crs_in <= value;
      endmethod
   endinterface
	    
endmodule

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package EthMac;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import BGetPut::*;
import Clocks::*;
import Control::*;
import EthFrame::*;
import EthMacConfigs::*;
import FIFO::*;
import FIFOF::*;
import GetPut::*;
import Mac::*;
import Mii::*;
import Randomizeable::*;
import Scoreboard::*;
import StmtFSM::*;
import TbEnvConfigs::*;
import Util::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface EthMacIFC;
   interface Control cntrl;
   interface EthMacConfigs cfg;
   interface FrameTxRxIFC macMacIFC;
   interface FrameBTxRxIFC macPhyIFC;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkEthMac#(Bool full_duplex, Scoreboard scoreboard, IndicationsIFC phy_indications) 
   (Clock phy_clk, Reset phy_reset, EthMacIFC ignore);
	 
   EthMacConfigs self <- mkEthMacConfigs;

   FIFO#(Frame) mac_tx <- mkFIFO;
   FIFOF#(Frame) mac_rx <- mkFIFOF;

   FIFOF#(Frame) phy_tx <- mkFIFOF1;
   FIFO#(Frame) phy_rx <- mkFIFO1;

   Reg#(Bool) deferring        <- mkReg(False);
   Reg#(Bool) transmitting     <- mkReg(False);
   Reg#(Bool) was_transmitting <- mkReg(False);
   Reg#(Bool) timeout          <- mkReg(False);

   Reg#(Bit#(8))  n_attempts   <- mkReg(0);
   Reg#(Bit#(32)) log_backoff  <- mkReg(0);
   Reg#(Bit#(32)) backoff      <- mkReg(0);
   Reg#(Bool)    success       <- mkReg(False);
   
   Reg#(Frame)   ignore        <- mkReg(?);
   
//   Reg#(Indications) indicate <- mkReg(Indications {collision: False, carrier: True});
   
   Reg#(Indications) indicate <- mkSyncRegToCC(Indications {collision: False, carrier: True},
					       phy_clk, phy_reset);
   
   Randomize#(Bit#(32)) backoff_gen <- mkGenericRandomizer;
   
   function ActionValue#(Bit#(32)) get_backoff ();
      actionvalue
	 let value <- backoff_gen.next;
	 let shift = 32 - (log_backoff - 1);
	 Bit#(32) out = (value << shift) >> shift;
	 return out;
      endactionvalue
   endfunction
   
   function ActionValue#(Bit#(32)) get_backoff_max ();
      actionvalue
	 return (32'b1 << (log_backoff - 1));
      endactionvalue
   endfunction
   
   rule update_indications;
      indicate <= phy_indications.indicate();
   endrule
   

   rule rx_monitor;
      let value = phy_rx.first();
      phy_rx.deq();

      if (self.promiscuous || (self.addr == value.dst) || (value.dst[47] == 1'b1))
	 begin
	    $display("(MAC): Received frame transmitted (%5d).",  $time);
	    mac_tx.enq(value);
	 end
      else
	 begin
            $display("(MAC): Received frame ignored because of wrong unicast address (%5d).",  $time);
	 end
   endrule

   rule check_for_collisions (indicate.collision);
      success <= False;
   endrule
   
   Stmt tx_driver_seq =
   seq
      while (True)
	 seq
	    action
	       let frame = mac_rx.first();
	       ignore <= frame;
	       n_attempts <= 0;
	       log_backoff <= 1;
	       success <= False;
	       $display("(%5d) Frame received in MAC.", $time);
	       displayFrame(frame);
	    endaction
	    while ((n_attempts < self.attempt_limit) && !success)
	       seq
		  action
		     $display("(instance %m): Attempting to transmit frame from mac to phy ... (%5d)",  $time);
		     $display("(instance %m):   Attempt #%0d: ",  n_attempts);
		  endaction
		  if (n_attempts > 0)
		     action
			let value <- get_backoff;
			let max <- get_backoff_max;
			backoff <= value;
			$display("(instance %m): Backing off for %0d slot times (max %0d) ... (%d cycles)",  value, max, (value * self.slot_time));
		     endaction
		  if (n_attempts > 0) delay(backoff * self.slot_time);
		  await(!deferring);
		  action
		     let frame = mac_rx.first();
		     phy_tx.enq(frame);
		     success <= True;
		     transmitting <= True;
		     log_backoff <= min(2, (log_backoff + 1));
//		     log_backoff <= (log_backoff + 1);
		  endaction
		  await(!phy_tx.notEmpty); // wait until frame has been transmitted (or a collision has occured)
		  action
		     transmitting <= False;
		     n_attempts <= n_attempts + 1;
		  endaction
	       endseq
	    action
	       let frame = mac_rx.first();
	       scoreboard.sent_from_phy_side(frame);
	       mac_rx.deq();
	    endaction
	 endseq
   endseq;

   Stmt deference_seq = // this is different form implementation in SV version. 
                        // The code for waiting for CRS to be deasserted has been 
                        // moved to the phy module.
   seq
      while (True)
	 seq
	    deferring <= False;
	    await(transmitting);
	    deferring <= True;
	    await(!transmitting);
	    delay(self.ifg);
	 endseq
   endseq;

   let tx_driver_fsm <- mkFSM(tx_driver_seq);
   let deference_fsm <- mkFSM(deference_seq);

   interface Control cntrl;
      method Action init();
	 self.cntrl.init;
	 backoff_gen.cntrl.init;
	 tx_driver_fsm.start;
	 deference_fsm.start;
	 mac_rx.clear;
      endmethod
   endinterface

   interface EthMacConfigs cfg;
      interface Control cntrl;
	 method Action init();
	    self.cntrl.init;
	 endmethod
      endinterface
      method _read = self._read;
   endinterface

   interface FrameTxRxIFC macMacIFC;
      interface Get tx = fifoToGet(mac_tx);
      interface Put rx;
	 method Action put (x);
	    mac_rx.enq(x);
	 endmethod
      endinterface
   endinterface

   interface FrameBTxRxIFC macPhyIFC;
      interface BGet tx = fifofToBGet(phy_tx);
      interface Put rx = fifoToPut(phy_rx);
   endinterface

endmodule

endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////



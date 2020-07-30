package SimpleSwitch;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Arbiter::*;
import Bank::*;
import Connectable::*;
import Control::*;
import EthFrame::*;
import GetPut::*;
import Randomizeable::*;
import Slice::*;
import WBone::*;
import Clocks::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module mkSimpleSwitch (Empty);
   
   // divide the clock
   ClockDividerIfc divClock <- mkClockDivider(10);
   
   Clock phy_clk = divClock.slowClock ;
   Reset phy_reset <- mkAsyncResetFromCR(3, phy_clk);

   Arbiter_IFC#(2) arbiter <- mkArbiter;
   Bank_IFC#(2)    bank    <- mkBank;
   
   Reg#(Bool) initialized <- mkReg(False);
   
   // a simple function to calculate a destination port for each frame.
   function Bit#(32) get_addr (Frame frame);
      return calculatePortAddress(2, frame);
   endfunction
   
   /// create a couple factories of ethernet Frames
   Randomize#(Frame) frame_src0 <- mkRandomizer;
   Randomize#(Frame) frame_src1 <- mkRandomizer;
   
   Slice_IFC slice0  <- 
   mkSlice(0, get_addr, bank.clients[0], arbiter.clients[0], phy_clk, phy_reset);
   Slice_IFC slice1  <- 
   mkSlice(1, get_addr, bank.clients[1], arbiter.clients[1],  phy_clk, phy_reset);
   
   mkConnection(randomizeToGet(frame_src0), slice0.channel.rx);
   mkConnection(randomizeToGet(frame_src1), slice1.channel.rx);
   
   let ifc_list = List::cons(slice0.master,
			     List::cons(slice1.master,
				List::cons(slice0.slave,
				   List::cons(slice1.slave,
				      List::nil))));
   
   mkWBoneZBus(ifc_list);
   
   rule sink_0;
      let frame <- slice0.channel.tx.get;
   endrule
   
   rule sink_1;
      let frame <- slice1.channel.tx.get;
   endrule
   
   rule initialize (!initialized);
      frame_src0.cntrl.init;
      frame_src1.cntrl.init;
      slice0.cntrl.init;
      slice1.cntrl.init;
      initialized <= True;
   endrule
   
endmodule


endpackage

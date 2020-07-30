package Slice;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Arbiter::*;
import Bank::*;
import Clocks::*;
import Connectable::*;
import Control::*;
import DutWrapped::*;
import EthFrame::*;
import FIFO::*;
import GetPut::*;
import WBAssemble::*;
import WBMaster::*;
import WBSerializer::*;
import WBSlave2::*;
import WBTransmit::*;
import WBone::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface Slice_IFC;
   interface Control         cntrl;
   interface FrameTxRxIFC    channel;
   interface WBoneZBusBusIFC master;
   interface WBoneZBusBusIFC slave;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkSlice#(Integer id, 
		function Bit#(32) get_addr(Frame frame),
		BankClient_IFC bank,
		ArbiterClient_IFC arbiter) 
   (Clock phy_clk, Reset phy_reset, Slice_IFC ignore);

   WBSerializerIFC serializer <- mkWBSerializer(id, get_addr);
		   
   WBTransmitIFC wb_transmit <- mkWBTransmit(id, bank);

   mkConnection(serializer.tx, wb_transmit.channel.rx);
   
   WBoneXActorIFC wb_master <- mkWBMaster(id , arbiter);
		   
   mkConnection(wb_transmit.wb_channel, wb_master.channel);
   
   WBoneXActorIFC wb_slave  <- mkWBSlave2(id,id);
   WBAssembleIFC wb_assemble <- mkWBAssemble(id);
		   
   mkConnection(wb_slave.channel, wb_assemble.wb_channel);
		   
   DutWrapped_IFC dut_wrapped <- mkDutWrapped(phy_clk, phy_reset);
   
   mkConnection(dut_wrapped.bus_channel.tx, serializer.rx);
   mkConnection( wb_assemble.tx, dut_wrapped.bus_channel.rx);
		   
   interface Control cntrl;
      method Action init();
	 serializer.cntrl.init;
	 wb_transmit.cntrl.init;
	 wb_assemble.cntrl.init;
	 wb_master.cntrl.init;
	 wb_slave.cntrl.init;
	 dut_wrapped.cntrl.init;
      endmethod
   endinterface
		   
   interface FrameTxRxIFC channel = dut_wrapped.channel;
		   
   interface WBoneZBusBusIFC master = wb_master.bus;
   interface WBoneZBusBusIFC slave  = wb_slave.bus;

      
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage
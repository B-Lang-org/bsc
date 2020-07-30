package DutWrapped;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Arbiter::*;
import BGetPut::*;
import Clocks::*;
import Connectable::*;
import Control::*;
import DutInit::*;
import EthFrame::*;
import EthMac::*;
import EthMacConfigs::*;
import EthTop::*;
import GetPut::*;
import Mii::*;
import MiiPhyLayer::*;
import Randomizeable::*;
import SWEmulator::*;
import Scoreboard::*;
import SimpleRam::*;
import StmtFSM::*;
import SyncConnectable::*;
import TbEnvConfigs::*;
import TbTop::*;
import TxRxPntArray::*;
import Util::*;
import WBMaster::*;
import WBRam::*;
import WBSlave::*;
import WBone::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface DutWrapped_IFC;
   interface Control cntrl;
   interface FrameTxRxIFC bus_channel;
   interface FrameTxRxIFC channel;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module mkDutWrapped (Clock phy_clk, Reset phy_reset, DutWrapped_IFC ignore);
   
   let clk <- exposeCurrentClock;
   let reset <- exposeCurrentReset;

`ifdef DYNAMIC_DUPLEX
   Reg#(Bool) full_duplex <- mkReg(False);
`else
   Reg#(Bool) full_duplex =
       interface Reg
	  method _read()   = False;
	  method _write(x) = noAction;
       endinterface;
`endif
   
   SyncPulseIfc init_phy <- mkSyncHandshakeFromCC(phy_clk);

   TbEnvConfigs self <- mkTbEnvConfigs;

   MiiPhyLayerIFC phy <- mkMiiPhyLayer(full_duplex, clocked_by(phy_clk), reset_by(phy_reset));
   
   Scoreboard scoreboard <- mkDummyScoreboard;

   EthMacIFC mac <- mkEthMac(full_duplex, scoreboard, phy.indications, phy_clk, phy_reset);
   
   mkSyncConnection(mac.macPhyIFC.tx, phy.frame_channel.rx, clk, reset, phy_clk, phy_reset);
   mkSynCConnection(mac.macPhyIFC.rx, phy.frame_channel.tx, clk, reset, phy_clk, phy_reset);
   
   Arbiter_IFC#(1) arbiter <- mkArbiter; // does nothing in this case (1 master)

   WBoneRamIFC    ram  <- mkWBRam(self);
   WBoneXActorIFC slv  <- mkWBSlave;
   mkConnection(ram.channel, slv.channel);
   
   WBoneXActorIFC host <- mkWBMaster(0, arbiter.clients[0]);

   TbTopIFC dut <- mkTbTop(phy_clk, phy_reset);
   
   /// Create a wishbone bus tying the various masters/slaves together.
   let ifc_list_0 = List::cons(host.bus,
			       List::cons(dut.slave,
					  List::nil));

   let ifc_list_1 = List::cons(slv.bus,
			       List::cons(dut.master, 
					  List::nil));
   
   mkWBoneZBus(ifc_list_0);
   mkWBoneZBus(ifc_list_1);

   /// create a couple factories of ethernet Frames
   let mac_cfg = mac.cfg;

   TxRxPntArrayIFC tx_rx_pnt_array <- mkTxRxPntArray(self, host);

   SWEmulatorIFC swem <- mkSWEmulator(self, ram.ram, tx_rx_pnt_array.ram, scoreboard);

   mkConnection(swem.wb_channel, host.channel);
   mkConnection(ram.channel, slv.channel);

   mkConnection(phy.mii_nibble_channel, dut.mii_nibble_channel);
   
   DutInitIFC dut_initializer <- 
   mkDutInit(self ,mac, full_duplex, host, init_phy);

   rule connect_int;
      swem.int_in(dut.int_out());
   endrule
   
   rule connect_indications;
      dut.coll_in(phy.indications.indicate.collision);
      dut.crs_in(phy.indications.indicate.carrier);
   endrule
   
   rule phy_init (init_phy.pulse);
      phy.cntrl.init;
   endrule

   interface Control cntrl;
      method Action init();
	 self.cntrl.init;
	 ram.cntrl.init;
	 slv.cntrl.init;
	 host.cntrl.init;
	 mac.cntrl.init;
	 tx_rx_pnt_array.cntrl.init;
	 swem.cntrl.init;
	 dut_initializer.cntrl.init;
	 scoreboard.cntrl.init;
      endmethod
   endinterface

   interface FrameTxRxIFC bus_channel;
      interface Get tx = swem.frame_channel.tx;
      interface Put rx = swem.frame_channel.rx;
   endinterface

   interface FrameTxRxIFC channel;
      interface Get tx = mac.macMacIFC.tx;
      interface Put rx = mac.macMacIFC.rx;
   endinterface

endmodule

endpackage

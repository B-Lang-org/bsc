package DutInit;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Clocks::*;
import Control::*;
import EthMac::*;
import EthMacConfigs::*;
import GetPut::*;
import Randomizeable::*;
import StmtFSM::*;
import TbEnvConfigs::*;
import WBMaster::*;
import WBone::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface DutInitIFC;
   interface Control cntrl;
   interface WBoneZBusBusIFC bus;
   method Bool done();
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkDutInit#(TbEnvConfigs parent, EthMacIFC mac, 
		  Reg#(Bool) full_duplex, WBoneXActorIFC host, SyncPulseIfc init_phy) 
   (DutInitIFC);
		  
   let mac_cfg = mac.cfg;
   
   Reg#(Bool) initialized <- mkReg(False);
		  
   Randomize#(WBoneOp) wboneop_gen <- mkRandomizer;
   
   Stmt dut_init_seq =
   seq
      action
	 $display("Starting DUT init sequence.");
	 Bool duplex <- $test$plusargs("full_duplex");
	 full_duplex <= duplex;
      endaction
      action // MODER
	 let wboneop <- wboneop_gen.next;
	 let val = 17'b1_1110_0000_0100_0000;
	 val[14:14] = pack(parent.huge_enable);
	 val[10] = pack(full_duplex);
	 val[5] = pack(mac_cfg.promiscuous);
	 val[16] = 1; //Enable receiving small packets (MODIFICATION 0)
	     
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h0000_0000}, tag: unpack(0) };
	 wboneop.data = BusData { data: {0, val},           tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
	 if (wboneop.status != ACK) $display( "Unable to write to MODER");
      endaction
      action // INT_MASK
	 let wboneop <- wboneop_gen.next;
	 let val = 32'h0000_000F;
	 
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h8}, tag: unpack(0) };
	 wboneop.data = BusData { data: {0, val}  , tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
	 if (wboneop.status != ACK) $display( "Unable to write to INT_MASK");
      endaction
      action // IPGT
	 let wboneop <- wboneop_gen.next;
	 Bit#(16) val;
	 if (full_duplex) 
	    val = 16'h15;
	 else 
	    val = 16'h12;
	 
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h0000_000C}, tag: unpack(0) };
	 wboneop.data = BusData { data: {0, val},           tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
      endaction

      action // PACKETLEN
	 let wboneop <- wboneop_gen.next;
	 
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h0000_0018},                 tag: unpack(0) };
	 wboneop.data = BusData { data: {0, 16'h000F, parent.max_frame_len}, tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
      endaction

      action // TX_BD_NUM
	 let wboneop <- wboneop_gen.next;
	 let val = parent.rx_bd_offset;
	 
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h0000_0020}, tag: unpack(0) };
	 wboneop.data = BusData { data: {0, val},           tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
      endaction
      action // CTRLMODER
	 let wboneop <- wboneop_gen.next;
	 let val = 32'b0111;
	 
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h0000_0024}, tag: unpack(0) };
	 wboneop.data = BusData { data: {0, val},           tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
      endaction
      action // MAC_ADDR0
	 let wboneop <- wboneop_gen.next;
	 let val = parent.dut_addr;
	 
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h0000_0040}, tag: unpack(0) };
	 wboneop.data = BusData { data: {0, val[31:0]},     tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
      endaction
      
      action // MAC_ADDR1
	 let wboneop <- wboneop_gen.next;
	 let val = parent.dut_addr;
	 
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h0000_0044}, tag: unpack(0) };
	 wboneop.data = BusData { data: {0, val[47:32]},    tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
      endaction
      delay(1000);
      action // MODER
	 Bool receive <- $test$plusargs("receive");
	 Bool transmit <- $test$plusargs("transmit");
	 if (receive) $display("Turn on receive mode.");
	 if (transmit) $display("Turn on transmit mode.");
	 let wboneop <- wboneop_gen.next;
	 let val = 17'b1_1110_0000_0100_0000;
	 if (receive) val[0:0] = 1'b1;
	 if (transmit) val[1:1] = 1'b1;
	 val[14:14] = pack(parent.huge_enable);
	 val[10] = pack(full_duplex);
//	 val[5] = pack(mac_cfg.promiscuous);
	 val[5] = 'b1;
	 
	 wboneop.kind = WRITE;
	 wboneop.addr = BusAddr { data: {0, 32'h0000_0000}, tag: unpack(0) };
	 wboneop.data = BusData { data: {0, val},           tag: unpack(0) };
	 wboneop.sel = unpack({0,4'hF});
	 host.channel.rx.put(wboneop);
      endaction
      action
	 let wboneop <- host.channel.tx.get;
      endaction
      init_phy.send;
      delay(100);
      initialized <= True;
      $display("DUT init sequence completed.");
   endseq;
   
   let dut_init_fsm <- mkFSM(dut_init_seq);
   
   interface Control cntrl;
      method Action init();
	 wboneop_gen.cntrl.init;
	 dut_init_fsm.start();
      endmethod
   endinterface
   
   interface WBoneZBusBusIFC bus = host.bus;
      
   method Bool done();
      return initialized;
   endmethod

endmodule

endpackage
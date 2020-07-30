
package TxRxPntArray;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import SimpleRam::*;
import RegFile::*;
import Control::*;
import WBone::*;
import StmtFSM::*;
import Randomizeable::*;
import GetPut::*;
import TbEnvConfigs::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef SimpleRamIFC#(Bit#(32), Bit#(32)) TxRxPntArrayRamIFC;

interface TxRxPntArrayIFC;
   interface Control cntrl;
   interface TxRxPntArrayRamIFC ram;
endinterface
      
module mkTxRxPntArray#(TbEnvConfigs parent, WBoneXActorIFC host) (TxRxPntArrayIFC);

   Reg#(Bool) initialized <- mkReg(False);

   RegFile#(Bit#(8) , Bit#(32)) mem <- mkRegFile(minBound, maxBound);

   Reg#(Bit#(16)) i <- mkReg(0);
   Reg#(Bit#(32)) bd_addr <- mkReg(0);


   /// create a factory of wishbone ops so we can randomize all the
   /// values that aren't tied down.
   Randomize#(WBoneOp) wboneop_gen <- mkRandomizer;

   let offset = 32'h0000_0400;

   Stmt init_seq = seq // Initialize the required number of buffer descriptors
		      $display("Starting TxRxPntArray init sequence (%0d)", $time);
		      bd_addr <= 32'h0000_0400;
		      for (i <= {0, parent.n_tx_bd}; i > 0; i <= i - 1)
			 seq
			    action
			       let wboneop <- wboneop_gen.next();
			       Bit#(32) val = 32'h0000_4000;
			       if (i == 1) val[13] = 1'b1;
			       wboneop.kind = WRITE;
			       wboneop.addr = BusAddr { data: {0, bd_addr}, tag: unpack(0) };
			       wboneop.data = BusData { data: {0, val}    , tag: unpack(0) };
			       wboneop.sel = unpack({0,4'hF});
			       host.channel.rx.put(wboneop);
			    endaction
			    action
			       let wboneop <- host.channel.tx.get();
			    endaction
			    action
			       let addr_mapped = truncate((bd_addr - offset) >> 3);
			       Bit#(32) val = parent.txrx_bfr_base + {0, (i * parent.max_frame_len)};
			       if (!initialized) mem.upd(addr_mapped, val);
			       bd_addr <= bd_addr + 4;
			    endaction
			    action
			       let wboneop <- wboneop_gen.next();
			       Bit#(32) val = parent.txrx_bfr_base + {0, (i * parent.max_frame_len)};
			       wboneop.kind = WRITE;
			       wboneop.addr = BusAddr { data: {0, bd_addr}, tag: unpack(0) };
			       wboneop.data = BusData { data: {0, val}    , tag: unpack(0) };
			       wboneop.sel = unpack({0,4'hF});
			       host.channel.rx.put(wboneop);
			       bd_addr <= bd_addr + 4;
			       $display("TX i = %d, val = %h", i, val);
			    endaction
			    action
			       let wboneop <- host.channel.tx.get();
			    endaction
			 endseq
		      bd_addr <= 32'h0000_0400 + {0, (parent.rx_bd_offset * 8)};
		      for (i <= {0, parent.n_rx_bd}; i > 0; i <= i - 1)
			 seq
			    action
			       let wboneop <- wboneop_gen.next();
			       Bit#(32) val = 32'h0000_0000;
			       val[15] = 1; // Empty
			       val[14] = 1; // Generate an interrupt
			       if (i == 1) val[13] = 1'b1;
			       wboneop.kind = WRITE;
			       wboneop.addr = BusAddr { data: {0, bd_addr}, tag: unpack(0) };
			       wboneop.data = BusData { data: {0, val}    , tag: unpack(0) };
			       wboneop.sel = unpack({0,4'hF});
			       host.channel.rx.put(wboneop);
			    endaction
			    action
			       let wboneop <- host.channel.tx.get();
			       if (wboneop.status != ACK) $display("Error 3. Non-ACK detected.");
			    endaction
			    action
			       let addr_mapped = truncate((bd_addr - offset) >> 3);
			       Bit#(32) val = parent.txrx_bfr_base + {0, (({0, parent.n_tx_bd} + i) * parent.max_frame_len)};
			       if (!initialized) mem.upd(addr_mapped, val);
			       bd_addr <= bd_addr + 4;
			    endaction
			    action
			       let wboneop <- wboneop_gen.next();
			       Bit#(32) val = parent.txrx_bfr_base + {0, (({0, parent.n_tx_bd} + i) * parent.max_frame_len)};
			       wboneop.kind = WRITE;
			       wboneop.addr = BusAddr { data: {0, bd_addr}, tag: unpack(0) };
			       wboneop.data = BusData { data: {0, val}    , tag: unpack(0) };
			       wboneop.sel = unpack({0,4'hF});
			       host.channel.rx.put(wboneop);
			       bd_addr <= bd_addr + 4;
			       $display("RX i = %d, val = %h", i, val);
			    endaction
			    action
			       let wboneop <- host.channel.tx.get();
			    endaction
			 endseq
		      $display("TxRxPntArray init sequence complete (%0d)", $time);
		      initialized <= True;
		   endseq;

   let init_fsm <- mkFSM(init_seq);

   
   interface Control cntrl;
      method Action init ();
	 wboneop_gen.cntrl.init();
	 init_fsm.start();
      endmethod
   endinterface

   interface TxRxPntArrayRamIFC ram;
      method Bit#(32) read (Bit#(32) addr) if (initialized);
	 let addr_mapped = truncate((addr - offset) >> 3);
	 return mem.sub(addr_mapped);
      endmethod

      method Action write (Bit#(32) addr, Bit#(32) data) if (initialized);
	 let addr_mapped = truncate((addr - offset) >> 3);
	 mem.upd(addr_mapped, data);
      endmethod
   endinterface

endmodule
   
endpackage

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////


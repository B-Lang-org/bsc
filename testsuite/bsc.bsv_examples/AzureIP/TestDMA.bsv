package TestDMA;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import BUtils::*;
import CBus::*;
import Connectable::*;
import DMADefines::*;
import FIFO::*;
import GetPut::*;
import Probe::*;
import Randomizable::*;
import SpecialFIFOs::*;
import StmtFSM::*;
import TLM::*;
import TLMDMA::*;
import Vector::*;

`include "TLM.defines"

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module sysTestDMA ();
   
   Reg#(Bit#(16)) count <- mkReg(0);
   
   TLMReadWriteSendIFC#(`TLM_STD_TYPES) source <- mkDMARequestSource;
   TLMDMAIFC#(`TLM_STD_TYPES)  dma <- mkTLMDMA;
   
   TLMTransformIFC#(`TLM_STD_TYPES) reducer <- mkTLMReducer;
   
   mkConnection(source, dma.slave);
   
   TLMReadWriteRecvIFC#(`TLM_STD_TYPES) mem  <- mkTLMReadWriteRam(0, True);
   
   mkConnection(dma.master.read, reducer.in);
   mkConnection(reducer.out, mem.read);
   mkConnection(dma.master.write, mem.write);
   
   rule every;
      count <= count + 1;
      if (count == 500) $finish;
   endrule
   
endmodule

// a source to generate DMA requests (through the config regs)
(* synthesize *)
module mkDMARequestSource (TLMReadWriteSendIFC#(`TLM_STD_TYPES));
   
   Reg#(TLMId#(`TLM_STD_TYPES))        count         <- mkReg(0);
   Reg#(Vector#(NumChannels, Bool))    active        <- mkReg(replicate(False));
   Reg#(Bit#(12))                      i             <- mkReg(0);
   Randomize#(TransferDescriptorStd)   gen           <- mkRandomizer;

   FIFO#(TransferDescriptorStd)        fifo_desc     <- mkBypassFIFO;
   
   FIFO#(TLMRequest#(`TLM_STD_TYPES))  read_tx_fifo  <- mkBypassFIFO;
   FIFO#(TLMResponse#(`TLM_STD_TYPES)) read_rx_fifo  <- mkBypassFIFO;
   FIFO#(TLMRequest#(`TLM_STD_TYPES))  write_tx_fifo <- mkBypassFIFO;
   FIFO#(TLMResponse#(`TLM_STD_TYPES)) write_rx_fifo <- mkBypassFIFO;
   
   let inum = valueOf(NumChannels);
      
   let test_seq =
   seq   
      gen.cntrl.init;
      while (True)
	 for (i <= 0; i < fromInteger(inum); i <= i + 1)
	    seq
	       if (active[i])
		  seq
		     // Check if the channel is still active and update the flag
		     action
			let request = createBasicRequestDescriptor;
			request.command = READ;
			let dc_addr = calculateDCAddrForChannel(activeAddrBase, i);
			let addr = createConfigRegAddr(dc_addr);
			request.addr = addr;
			request.transaction_id = count;
			count <= count + 1;
			read_tx_fifo.enq(tagged Descriptor request);
      		     endaction
		     action
			let response = read_rx_fifo.first;
			read_rx_fifo.deq;
			let value = response.data;
			active[i] <= unpack(value[0]);
		     endaction
		  endseq
	       if (!active[i])
		  seq
		     // Generate a new transfer descriptor and write it to the config reg
		     action
			let value <- gen.next;
			let request = createBasicRequestDescriptor;
			request.command = WRITE;
			let dc_addr = calculateDCAddrForChannel(descriptorAddrBase, i);
			let addr = createConfigRegAddr(dc_addr);
			request.addr = addr;
			request.transaction_id = count;
			count <= count + 1;
			request.data = cExtend(pack(value));
			write_tx_fifo.enq(tagged Descriptor request);
		     endaction
		     action
			let response = write_rx_fifo.first;
			write_rx_fifo.deq;
		     endaction
		     // Mark the channel as active.
		     action
			let request = createBasicRequestDescriptor;
			request.command = WRITE;
			let dc_addr = calculateDCAddrForChannel(activeAddrBase, i);
			let addr = createConfigRegAddr(dc_addr);
			request.addr = addr;
			request.transaction_id = count;
			count <= count + 1;
			request.data = cExtend(1);
			active[i] <= True;
			write_tx_fifo.enq(tagged Descriptor request);
		     endaction
		     action
			let response = write_rx_fifo.first;
			write_rx_fifo.deq;
		     endaction
		  endseq
	    endseq
   endseq;
   
   let fsm <- mkAutoFSM(test_seq);
      
   interface TLMSendIFC read;
      interface Get tx = toGet(read_tx_fifo);
      interface Put rx = toPut(read_rx_fifo);
   endinterface
   interface TLMSendIFC write;
      interface Get tx = toGet(write_tx_fifo);
      interface Put rx = toPut(write_rx_fifo);
   endinterface

   
endmodule

function TLMAddr#(`TLM_STD_TYPES) createConfigRegAddr(DCAddr addr);
   let value = ({0, addr.a} | 13'h1000);
   return cExtend(value);
endfunction

endpackage
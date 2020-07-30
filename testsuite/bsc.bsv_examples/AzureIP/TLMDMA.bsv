package TLMDMA;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import BUtils::*;
import CBus::*;
import DMAConfigRegs::*;
import DMADefines::*;
import FIFO::*;
import GetPut::*;
import SpecialFIFOs::*;
import TLM::*;

`include "TLM.defines"

////////////////////////////////////////////////////////////////////////////////
// Define the master and slave interfaces, as defined in the TLM package
////////////////////////////////////////////////////////////////////////////////

interface TLMDMAIFC#(`TLM_TYPE_PRMS);
   interface TLMReadWriteSendIFC#(`TLM_TYPES) master;
   interface TLMReadWriteRecvIFC#(`TLM_TYPES) slave;
endinterface

(* synthesize *)
// The mkTLMDMA module header:
module mkTLMDMA (TLMDMAIFC#(`TLM_STD_TYPES));

// Initialize status registers. The DMA starts out in idle mode.   
   Reg#(Bool) idle <- mkReg(True);
   Reg#(Bool) done <- mkReg(False);
   
///////////////////////////////////////////////////////////////////////////////
//  A block of configuration registers
///////////////////////////////////////////////////////////////////////////////
   
   let cfg <- mkDMAConfigRegs;
   let cfg_values = cfg.device_ifc; // just an alias!
   
///////////////////////////////////////////////////////////////////////////////
// An adapter to connect the config bus unit to the TLM slave interface 
// (defined in TLM)
///////////////////////////////////////////////////////////////////////////////
 
   TLMReadWriteRecvIFC#(`TLM_STD_TYPES) adapter <- 
                                mkTLMCBusAdapterToReadWrite(truncate, cfg.cbus_ifc);
   
///////////////////////////////////////////////////////////////////////////////
//  Instantiate 4 FIFOs for  read and write transactions
///////////////////////////////////////////////////////////////////////////////

// Request FIFO for read transactions   
   FIFO#(TLMRequestStd)  fifo_read_tx  <- mkBypassFIFO;
// Response FIFO for read transactions   
   FIFO#(TLMResponseStd) fifo_read_rx  <- mkBypassFIFO;

// Request FIFO for write transactions         
   FIFO#(TLMRequestStd)  fifo_write_tx <- mkBypassFIFO;
// Response FIFO for write transactions   
   FIFO#(TLMResponseStd) fifo_write_rx <- mkBypassFIFO;
   
// a channel FIFO to buffer the read responses to the write request side
   FIFO#(TLMData#(`TLM_STD_TYPES)) fifo_channel <- mkSizedFIFO(16);

// Local status registers
   Reg#(DescLen) reads_remaining  <- mkReg(0);
   Reg#(DescLen) writes_remaining <- mkReg(0);
   Reg#(TLMAddr#(`TLM_STD_TYPES)) addr <- mkReg(0);
   
// a few local definitions
   let active = (cfg_values.active[0] == 1);
   TransferDescriptor#(`TLM_STD_TYPES) current = 
      cExtend(cfg_values.descriptor[0]);
   
////////////////////////////////////////////////////////////////////////////   
// Rule to start the DMA transaction
// Sets idle to false, initializes reads_remaining and writes_remaining
// to the length of the burst, and addr to the destination address
////////////////////////////////////////////////////////////////////////////   

   rule start_transfer (idle && active);
      idle <= False;
      $display("(%0d) DMA: receiving descriptor (src: %h dst: %h len: %d)", $time, current.source, current.dest, current.length);
      reads_remaining <= current.length;
      writes_remaining <= current.length;
      addr <= cExtend(current.dest);
   endrule

////////////////////////////////////////////////////////////////////////////   
// Rule which generates a read request,
// and enqueues it to the fifo_read_tx
////////////////////////////////////////////////////////////////////////////   
   
   rule data_read (!done && active && !idle && (reads_remaining > 0));
      let read_count = min(reads_remaining, 16);
      let remaining = reads_remaining - read_count;
      reads_remaining <= remaining;
      let request = createBasicRequestDescriptor;
      request.command = READ;
      request.burst_length = cExtend(read_count);
      request.addr = cExtend(current.source);
      fifo_read_tx.enq(tagged Descriptor request);
   endrule

////////////////////////////////////////////////////////////////////////////   
// Rule which generates a write request,
// and enqueues it to the fifo_write_tx
////////////////////////////////////////////////////////////////////////////   
   
   rule data_write (!done && active && !idle && (writes_remaining > 0));
      let data = fifo_channel.first;
      fifo_channel.deq;
      let request = createBasicRequestDescriptor;
      request.command = WRITE;
      request.burst_length = 1;
      request.addr = addr;
      request.data = data;
      let update = incrTLMAddr(request);
      let remaining = writes_remaining - 1;
      writes_remaining <= remaining;
      addr <= update.addr;
      fifo_write_tx.enq(tagged Descriptor request);
      if (remaining == 0) done <= True;
   endrule
   
////////////////////////////////////////////////////////////////////////////   
// Rule to finish the transfer
// Sets done to False, idle to True
// resets the active value of the configuration register to 0
////////////////////////////////////////////////////////////////////////////   

   rule finish_transfer (done && !idle);
      done <= False;
      idle <= True;
      cfg_values.active[0] <= 0;
   endrule

////////////////////////////////////////////////////////////////////////////   
// Rule to get the read response
// Moves the read data into the fifo_channel 
////////////////////////////////////////////////////////////////////////////   
   
   rule get_read_response_data;
      let response = fifo_read_rx.first;
      fifo_read_rx.deq;
      fifo_channel.enq(response.data);
   endrule

////////////////////////////////////////////////////////////////////////////   
// Rule to get the write response
// Removes the write value from the fifo_channel 
////////////////////////////////////////////////////////////////////////////   
   
   rule get_write_response_data;
      let response = fifo_write_rx.first;
      fifo_write_rx.deq;
   endrule
   
////////////////////////////////////////////////////////////////////////////////
// Interface implementation
////////////////////////////////////////////////////////////////////////////////

   interface TLMReadWriteSendIFC master;
      interface TLMSendIFC  write;
         // connecting the Get side of fifo_write_tx to the main master interface
	 interface Get  tx = toGet(fifo_write_tx);
         // connecting the Put side of fifo_write_rx to the main master interface
         interface Put  rx = toPut(fifo_write_rx);
      endinterface
      interface TLMSendIFC  read;
         // connecting the Get side of fifo_read_tx to the main master interface
	 interface Get  tx = toGet(fifo_read_tx);
         // connecting the Put side of fifo_read_rx to the main master interface
	 interface Put  rx = toPut(fifo_read_rx);
      endinterface
   endinterface
   
   // stitching the adapter interface to the main slave interface
   interface TLMReadWriteRecvIFC slave = adapter;
   
endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////
   
endpackage

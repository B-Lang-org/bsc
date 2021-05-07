// Copyright (c) 2020 Bluespec, Inc. All rights reserved.
//
// SPDX-License-Identifier: BSD-3-Clause

package TLMDefines;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Connectable::*;
import FIFO::*;
import FShow::*;
import GetPut::*;
import Randomizable::*;
import BUtils::*;
import Vector::*;

`include "TLM.defines"

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef TLMRequest#(`TLM_STD_TYPES)  TLMRequestStd;
typedef TLMResponse#(`TLM_STD_TYPES) TLMResponseStd;

typedef enum {READ, WRITE, UNKNOWN}               TLMCommand   deriving(Bounded, Bits, Eq);
typedef enum {REGULAR, DEBUG, CONTROL}            TLMMode      deriving(Bounded, Bits, Eq);
typedef enum {INCR, CNST, WRAP, UNKNOWN} TLMBurstMode deriving(Bounded, Bits, Eq);
typedef enum {SUCCESS, ERROR, NO_RESPONSE}        TLMStatus    deriving(Bounded, Bits, Eq);

typedef Bit#(id_size)                    TLMId#(`TLM_TYPE_PRMS);
typedef Bit#(addr_size)                  TLMAddr#(`TLM_TYPE_PRMS);
typedef Bit#(data_size)                  TLMData#(`TLM_TYPE_PRMS);
typedef UInt#(uint_size)                 TLMUInt#(`TLM_TYPE_PRMS);
typedef Bit#(TDiv#(data_size, 8))        TLMByteEn#(`TLM_TYPE_PRMS);
typedef Bit#(TLog#(TDiv#(data_size, 8))) TLMBurstSize#(`TLM_TYPE_PRMS);
typedef cstm_type                        TLMCustom#(`TLM_TYPE_PRMS);

typedef struct {TLMCommand               command;
		TLMMode                  mode;
		TLMAddr#(`TLM_TYPES)     addr;
		TLMData#(`TLM_TYPES)     data;
		TLMUInt#(`TLM_TYPES)     burst_length;
		TLMByteEn#(`TLM_TYPES)   byte_enable;
		TLMBurstMode             burst_mode;
		TLMBurstSize#(`TLM_TYPES) burst_size;
		TLMUInt#(`TLM_TYPES)     prty;
		Bool                     lock;
		TLMId#(`TLM_TYPES)       thread_id;
		TLMId#(`TLM_TYPES)       transaction_id;
		TLMId#(`TLM_TYPES)       export_id;
		TLMCustom#(`TLM_TYPES)   custom;
		} RequestDescriptor#(`TLM_TYPE_PRMS) deriving (Eq, Bits, Bounded);

typedef struct {TLMData#(`TLM_TYPES)   data;
		TLMId#(`TLM_TYPES)     transaction_id;
		TLMCustom#(`TLM_TYPES) custom;
		} RequestData#(`TLM_TYPE_PRMS) deriving (Eq, Bits, Bounded);

typedef union tagged {RequestDescriptor#(`TLM_TYPES) Descriptor;
		      RequestData#(`TLM_TYPES)       Data;
		      } TLMRequest#(`TLM_TYPE_PRMS) deriving(Eq, Bits, Bounded);

typedef struct {TLMCommand             command;
		TLMData#(`TLM_TYPES)   data;
		TLMStatus              status;
		TLMUInt#(`TLM_TYPES)   prty;
		TLMId#(`TLM_TYPES)     thread_id;
		TLMId#(`TLM_TYPES)     transaction_id;
		TLMId#(`TLM_TYPES)     export_id;
		TLMCustom#(`TLM_TYPES) custom;
		} TLMResponse#(`TLM_TYPE_PRMS) deriving (Eq, Bits, Bounded);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

module mkTLMRandomizer#(Maybe#(TLMCommand) m_command) (Randomize#(TLMRequest#(`TLM_TYPES)))
   provisos(Bits#(RequestDescriptor#(`TLM_TYPES), s0),
	    Bounded#(RequestDescriptor#(`TLM_TYPES)),
	    Bits#(RequestData#(`TLM_TYPES), s1),
	    Bounded#(RequestData#(`TLM_TYPES))
	    );

   Reg#((TLMUInt#(`TLM_TYPES)))               count            <- mkReg(0);
   Randomize#(RequestDescriptor#(`TLM_TYPES)) descriptor_gen   <- mkGenericRandomizer;
   Randomize#(TLMCommand)                     command_gen      <- mkConstrainedRandomizer(READ, WRITE);     // Avoid UNKNOWN
   Randomize#(TLMBurstMode)                   burst_mode_gen   <- mkConstrainedRandomizer(INCR, WRAP); // Avoid UNKNOWN
   Randomize#(TLMUInt#(`TLM_TYPES))           burst_length_gen <- mkConstrainedRandomizer(1,16);            // legal sizes between 1 and 16
   Randomize#(Bit#(2))                        log_wrap_gen     <- mkGenericRandomizer;
   Randomize#(RequestData#(`TLM_TYPES))       data_gen         <- mkGenericRandomizer;
   Reg#(TLMId#(`TLM_TYPES))                   id               <- mkReg(0);

   Randomize#(Bit#(TLog#(SizeOf#(TLMBurstSize#(`TLM_TYPES))))) log_size_gen <- mkGenericRandomizer;

   interface Control cntrl;
      method Action init();
   //	    srand(0);
	 descriptor_gen.cntrl.init();
	 command_gen.cntrl.init();
	 burst_mode_gen.cntrl.init();
	 burst_length_gen.cntrl.init();
	 log_wrap_gen.cntrl.init();
	 data_gen.cntrl.init();
	 log_size_gen.cntrl.init();
      endmethod
   endinterface

   method ActionValue#(TLMRequest#(`TLM_TYPES)) next ();

      if (count == 0)
	 begin
	    let descriptor <- descriptor_gen.next;
	    let burst_mode <- burst_mode_gen.next;

	    descriptor.command <- command_gen.next;

	    let log_size <- log_size_gen.next;

	    descriptor.burst_size = ((1 << log_size) >> 1);

	    // align address to burst_size
	    let addr = descriptor.addr;
	    addr = addr >> log_size;
	    addr = addr << log_size;
	    descriptor.addr = addr;

	    if (burst_mode == WRAP)
	       begin
		  let shift <- log_wrap_gen.next;
		  let burst_length = 2 << shift; // wrap legal lengths are 2, 4, 8, 16
		  descriptor.burst_length = burst_length;
//		  addr = addr >> shift;
//		  addr = addr >> 1;
//		  addr = addr << shift;
//		  addr = addr << 1;
		  descriptor.addr = addr;
	       end
	    else
	       begin
		  let burst_length <- burst_length_gen.next;
		  descriptor.burst_length = burst_length;
	       end

	    descriptor.command = case (m_command) matches
				    tagged Just .x: x;
				    default       : descriptor.command;
				 endcase;

	    descriptor.mode = REGULAR;
	    descriptor.byte_enable = getTLMByteEn(descriptor);
	    descriptor.burst_mode = burst_mode;

	    descriptor.thread_id = 0;
	    descriptor.transaction_id = id;
	    descriptor.export_id = 0;

	    if (descriptor.command == READ)
	       begin
		  descriptor.data = 0;
		  descriptor.byte_enable = '1;
	       end

	    let request = tagged Descriptor descriptor;
	    let remaining = getTLMCycleCount(descriptor) - 1;
	    count <= remaining;
	    id <= (remaining == 0) ? id + 1 : id;
	    return request;
	 end
      else
	 begin
	    let data <- data_gen.next();
	    data.transaction_id = unpack({0, id});
	    let request = tagged Data data;
	    let remaining = count - 1;
	    count <= remaining;
	    id <= (remaining == 0) ? id + 1 : id;
	    return request;
	 end

   endmethod

endmodule

instance Randomizable#(TLMRequest#(`TLM_TYPES))
   provisos(Bits#(RequestDescriptor#(`TLM_TYPES), s0),
	    Bounded#(RequestDescriptor#(`TLM_TYPES)),
	    Bits#(RequestData#(`TLM_TYPES), s1),
	    Bounded#(RequestData#(`TLM_TYPES))
	    );

   module mkRandomizer (Randomize#(TLMRequest#(`TLM_TYPES)));
      let ifc <- mkTLMRandomizer(Invalid);
      return ifc;
   endmodule

endinstance

(* synthesize *)
module mkTLMSource#(Maybe#(TLMCommand) m_command, Bool verbose) (TLMSendIFC#(`TLM_STD_TYPES));

   Reg#(Bool)                initialized   <- mkReg(False);
   FIFO#(TLMResponseStd)     response_fifo <- mkFIFO;
   Randomize#(TLMRequestStd) gen           <- mkTLMRandomizer(m_command);

   rule start (!initialized);
      gen.cntrl.init;
      initialized <= True;
   endrule

   rule grab_responses;
      let value = response_fifo.first;
      response_fifo.deq;
      if (verbose) $display("(%0d) Response is: ", $time, fshow(value));
   endrule

   interface Get tx;
      method ActionValue#(TLMRequestStd) get;
	 let value <- gen.next;
	 if (value matches tagged Descriptor .d)
	    if (verbose) $display("(%0d) Request is: ", $time, fshow(d));
	 return value;
      endmethod
   endinterface

   interface Put rx = toPut(response_fifo);

endmodule

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function TLMUInt#(`TLM_TYPES) getTLMCycleCount (RequestDescriptor#(`TLM_TYPES) desc);
   if (desc.command == READ)
      return 1;
   else
      return desc.burst_length;
endfunction

function Bit#(n) getTLMBurstSize (RequestDescriptor#(`TLM_TYPES) desc)
   provisos(Add#(SizeOf#(TLMBurstSize#(`TLM_TYPES)), 1, n));
   return zExtend(desc.burst_size) + 1;
endfunction

function Bit#(n) getTLMIncr (RequestDescriptor#(`TLM_TYPES) desc)
   provisos(Add#(SizeOf#(TLMBurstSize#(`TLM_TYPES)), 1, n));
   if (desc.burst_mode == CNST)
      return 0;
   else
      return zExtend(desc.burst_size) + 1;
endfunction

function TLMByteEn#(`TLM_TYPES) getTLMByteEn (RequestDescriptor#(`TLM_TYPES) tlm_descriptor);
   Bit#(TLog#(SizeOf#(TLMByteEn#(`TLM_TYPES)))) addr = zExtend(tlm_descriptor.addr);
   TLMByteEn#(`TLM_TYPES) all_ones = unpack('1);
   let mask = ~(all_ones << (tlm_descriptor.burst_size + 1));

   return (mask << addr);
endfunction

function RequestDescriptor#(`TLM_TYPES) incrTLMAddr(RequestDescriptor#(`TLM_TYPES) desc);
   let incr = getTLMIncr(desc);
   let addr = desc.addr + cExtend(incr);
   if (desc.burst_mode == WRAP)
      begin
	 TLMAddr#(`TLM_TYPES) size     = zExtend(pack(desc.burst_size)) + 1;
	 TLMAddr#(`TLM_TYPES) length   = zExtend(pack(desc.burst_length));
	 let log_size   = countLSBZeros(size);
	 let log_length = countLSBZeros(length);
	 let total = log_size + log_length;
	 TLMAddr#(`TLM_TYPES) mask = (1 << total) - 1;
	 addr = (addr & mask) | (desc.addr & ~mask);
      end
   desc.addr = addr;
   return desc;
endfunction

function Bit#(n) countLSBZeros (Bit#(n) value);
   Vector#(n, Bool) vector_value = unpack(value);
   let pos = findIndex(id, vector_value);
   case (pos) matches
      tagged Valid .p: return zExtend(pack(p));
      tagged  Invalid: return fromInteger(valueOf(n));
   endcase

endfunction


function TLMData#(`TLM_TYPES) getTLMData(TLMRequest#(`TLM_TYPES) request);
   case (request) matches
      (tagged Descriptor .d): return d.data;
      (tagged Data .d)      : return d.data;
   endcase
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance FShow#(TLMCommand);
   function Fmt fshow (TLMCommand label);
      case (label)
	 READ:    return fshow("READ ");
	 WRITE:   return fshow("WRITE");
	 UNKNOWN: return fshow("UNKNOWN");
      endcase
   endfunction
endinstance

instance FShow#(TLMMode);
   function Fmt fshow (TLMMode label);
      case (label)
	 REGULAR: return fshow("REG");
	 DEBUG:   return fshow("DBG");
	 CONTROL: return fshow("CTL");
      endcase
   endfunction
endinstance

instance FShow#(TLMBurstMode);
   function Fmt fshow (TLMBurstMode label);
      case (label)
	 INCR: return fshow("INCR");
	 CNST: return fshow("CNST");
	 WRAP: return fshow("WRAP");
      endcase
   endfunction
endinstance

function Fmt fshowBurstMode (RequestDescriptor#(`TLM_TYPES) op);
   case (op.burst_mode)
	 INCR: return $format("INCR %0d", getTLMBurstSize(op));
	 CNST: return $format("CNST %0d", getTLMBurstSize(op));
	 WRAP: return $format("WRAP %0d", getTLMBurstSize(op));
      endcase
endfunction

instance FShow#(TLMStatus);
   function Fmt fshow (TLMStatus label);
      case (label)
	 SUCCESS:     return fshow("SUCCESS");
	 ERROR:       return fshow("ERROR  ");
	 NO_RESPONSE: return fshow("NO_RESP");
      endcase
   endfunction
endinstance

instance FShow#(RequestData#(`TLM_TYPES))
   provisos(Add#(ignore0, uint_size, 32));

   function Fmt fshow (RequestData#(`TLM_TYPES) data);
      return ($format("<TDATA [%0d]", data.transaction_id)
	      +
	      $format(" %h>", data.data));
   endfunction
endinstance

instance FShow#(RequestDescriptor#(`TLM_TYPES));

   function Fmt fshow (RequestDescriptor#(`TLM_TYPES) op);
      return ($format("<TDESC [%0d] ", op.transaction_id)
	      +
	      fshow(op.command)
	      +
	      fshow(" ")
	      +
	      fshowBurstMode(op)
	      +
	      $format(" (%0d)", op.burst_length)
	      +
	      $format(" A:%h", op.addr)
	      +
	      $format(" D:%h>", op.data));
   endfunction
endinstance

instance FShow#(TLMRequest#(`TLM_TYPES))
   provisos(FShow#(RequestData#(`TLM_TYPES)),
	    FShow#(RequestDescriptor#(`TLM_TYPES)));

   function Fmt fshow (TLMRequest#(`TLM_TYPES) request);
      case (request) matches
	 tagged Descriptor .a:
	    return fshow(a);
	 tagged Data .a:
	    return fshow(a);
      endcase
   endfunction
endinstance

instance FShow#(TLMResponse#(`TLM_TYPES));
   function Fmt fshow (TLMResponse#(`TLM_TYPES) op);
      return ($format("<TRESP [%0d] ", op.transaction_id)
	      +
	      fshow(op.command)
	      +
	      fshow(" ")
	      +
	      fshow(op.status)
	      +
	      $format(" %h>", op.data));
   endfunction
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface TLMSendIFC#(`TLM_TYPE_PRMS);
   interface Get#(TLMRequest#(`TLM_TYPES))  tx;
   interface Put#(TLMResponse#(`TLM_TYPES)) rx;
endinterface

interface TLMRecvIFC#(`TLM_TYPE_PRMS);
   interface Get#(TLMResponse#(`TLM_TYPES)) tx;
   interface Put#(TLMRequest#(`TLM_TYPES))  rx;
endinterface

interface TLMReadWriteSendIFC#(`TLM_TYPE_PRMS);
   interface TLMSendIFC#(`TLM_TYPES) read;
   interface TLMSendIFC#(`TLM_TYPES) write;
endinterface

interface TLMReadWriteRecvIFC#(`TLM_TYPE_PRMS);
   interface TLMRecvIFC#(`TLM_TYPES) read;
   interface TLMRecvIFC#(`TLM_TYPES) write;
endinterface

interface TLMTransformIFC#(`TLM_TYPE_PRMS);
   interface TLMRecvIFC#(`TLM_TYPES) in;
   interface TLMSendIFC#(`TLM_TYPES) out;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

instance Connectable#(TLMSendIFC#(`TLM_TYPES), TLMRecvIFC#(`TLM_TYPES));
   module mkConnection#(TLMSendIFC#(`TLM_TYPES) request, TLMRecvIFC#(`TLM_TYPES) response) (Empty);
      mkConnection(request.tx, response.rx);
      mkConnection(request.rx, response.tx);
   endmodule
endinstance

instance Connectable#(TLMRecvIFC#(`TLM_TYPES), TLMSendIFC#(`TLM_TYPES));
   module mkConnection#(TLMRecvIFC#(`TLM_TYPES) response, TLMSendIFC#(`TLM_TYPES) request) (Empty);
      mkConnection(request.tx, response.rx);
      mkConnection(request.rx, response.tx);
   endmodule
endinstance

instance Connectable#(TLMReadWriteSendIFC#(`TLM_TYPES), TLMReadWriteRecvIFC#(`TLM_TYPES));
   module mkConnection#(TLMReadWriteSendIFC#(`TLM_TYPES) request, TLMReadWriteRecvIFC#(`TLM_TYPES) response) (Empty);
      let read_con  <- mkConnection(request.read,  response.read);
      let write_con <- mkConnection(request.write, response.write);
   endmodule
endinstance

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typeclass Monitorable #(type a);
   module mkMonitor#(a ifc) (Empty);
endtypeclass

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typeclass AddrMatch#(type addr_t, type ifc_t);
   function ifc_t addAddrMatch(function Bool addrMatch(addr_t value), ifc_t value);
endtypeclass

function Bool alwaysAddrMatch(a value);
   return True;
endfunction

endpackage

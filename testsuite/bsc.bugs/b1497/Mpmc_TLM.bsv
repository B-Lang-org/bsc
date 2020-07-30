package Mpmc_TLM;

`include "MPMC.defines"

import GetPut::*;
import FIFO::*;
import TLM::*;
import SpecialFIFOs::*;

import Mpmc_NPI::*;

typedef struct {TLMCommand             command;
		TLMUInt#(`TLM_TYPES)   prty;
		TLMId#(`TLM_TYPES)     thread_id;
		TLMId#(`TLM_TYPES)     transaction_id;
		TLMId#(`TLM_TYPES)     export_id;
		TLMCustom#(`TLM_TYPES) custom;
		} SkeletonResp#(`TLM_TYPE_PRMS) deriving (Eq, Bits, Bounded);

interface NPISlaveXActorIFC#(`TLM_TYPE_PRMS);
   interface TLMRecvIFC#(`TLM_TYPES) tlm;
   interface NPI_Port_Client#(`TLM_TYPES)  npi;
endinterface

typedef enum { SAFE, SPECIAL } TransferMode deriving (Eq, Bits);

// For this version, we allow only the transactions which the MPMC supports;
// that is, we don't attempt to break down other TLM transactions into a
// sequence of supported transactions.

function UInt#(4) npiSize (RequestDescriptor#(`TLM_TYPES) d);
   UInt#(4) result = ?;
   let ll = d.burst_length;
   if (ll==1) result = 0;
   else
      begin
	 if (valueof(SizeOf#(TLMData#(`TLM_TYPES)))==64) ll = ll<<1;
	 case (ll)
	    4: result = 1;
	    8: result = 2;
	    16: result = 3;
	    32: result = 4;
	    64: result = 5;
	    default: result = error("Invalid TLM burst length");
	 endcase
      end
   return result;
endfunction

function TransferMode transferMode(RequestDescriptor#(`TLM_TYPES) d) =
    npiSize(d)==0 ? SPECIAL : SAFE;

function NPICmd#(`TLM_TYPES) npiCommand (RequestDescriptor#(`TLM_TYPES) d);
   NPICmd#(`TLM_TYPES) c = ?;
   c.rdModWr = False;
   c.addr = d.addr;
   c.rnw = (d.command==READ);
   c.size = npiSize(d);
   return c;
endfunction

function TLMUInt#(`TLM_TYPES) noOfItems (RequestDescriptor#(`TLM_TYPES) d) =
   d.burst_length;

function NPIWrArgs#(`TLM_TYPES) npiWrArgs (TLMRequest#(`TLM_TYPES) r);
   NPIWrArgs#(`TLM_TYPES) w = ?;
   case (r) matches
      tagged Descriptor .d:
	 begin
	    w.wrData = d.data;
	    w.wrBE = d.byte_enable;
	 end
      tagged Data .d:
	 begin
	    w.wrData = d.data;
	    w.wrBE = '1;
	 end
      endcase
   return w;
endfunction

function SkeletonResp#(`TLM_TYPES) skeleton(RequestDescriptor#(`TLM_TYPES) d);
   SkeletonResp#(`TLM_TYPES) r = ?;
   r.command = d.command;
   r.prty = d.prty;
   r.thread_id = d.thread_id;
   r.transaction_id = d.transaction_id;
   r.export_id = d.export_id;
   r.custom = d.custom;
   return r;
endfunction

function TLMResponse#(`TLM_TYPES) fleshOut(SkeletonResp#(`TLM_TYPES) s,
					   TLMData#(`TLM_TYPES)   d,
					   TLMStatus st);
   TLMResponse#(`TLM_TYPES) r = ?;
   r.command = s.command;
   r.prty = s.prty;
   r.thread_id = s.thread_id;
   r.transaction_id = s.transaction_id;
   r.export_id = s.export_id;
   r.custom = s.custom;
   r.data = d;
   r.status = st;
   return r;
endfunction

function TLMResponse#(`TLM_TYPES) tlmify(NPIRdResult#(`TLM_TYPES) x, 
					 SkeletonResp#(`TLM_TYPES) sk);
   let r = fleshOut(sk, x.rdData, SUCCESS);
   r.custom = x.rdWdAddr;
   return r;
endfunction

module mkNPISlaveXActor(NPISlaveXActorIFC#(`TLM_TYPES))
   provisos(Bits#(TLMCustom#(`TLM_TYPES), cs));
	    //Bits#(TLMRequest#(`TLM_TYPES), rs));

   let tlminff  <- mkBypassFIFO;
   let tlmoutff <- mkBypassFIFO;
   let wrDataFF <- mkBypassFIFO;
   let cmdFF    <- mkBypassFIFO;
   FIFO#(void) endWr <- mkBypassFIFO;

   Reg#(Maybe#(NPICmd#(`TLM_TYPES))) cmdBuf <- mkReg(Invalid);
   Reg#(TLMUInt#(`TLM_TYPES)) rdDataCnt <- mkReg(0);
   Reg#(TLMUInt#(`TLM_TYPES)) wrDataCnt <- mkReg(0);
   Reg#(Bool) writeResponsePending <- mkReg(False);
   // Bool canAcceptCommand = (wrDataCnt==0);
   Bool canAcceptWriteCommand = !writeResponsePending;
   FIFO#(SkeletonResp#(`TLM_TYPES)) skRspFF <- mkSizedFIFO(4); // max of 4 commands
				// allowed in flight
   FIFO#(TLMUInt#(`TLM_TYPES)) readSizesFF <- mkSizedFIFO(4);

   rule writing(canAcceptWriteCommand &&&
		tlminff.first matches tagged Descriptor .d &&& d.command==WRITE);
      let r = tlminff.first;
      let n = noOfItems(d);
      let c = npiCommand(d);
      skRspFF.enq(skeleton(d));
      if (transferMode(d)==SAFE)
	 // In this mode the write data are sent first, and the command is
	 // held back until the last item is sent.
	 begin
	    cmdBuf <= tagged Valid c;
	    wrDataCnt <= n;
	 end
      else // (transferMode(d)==SPECIAL)
	 // In this mode the command is sent first, and the data held back until
	 // the cycle after that is accepted.
	 begin
	    cmdFF.enq(tuple2(n, c)); // n is no. of data items to be sent later
	 end
      wrDataFF.enq(npiWrArgs(r));
      tlminff.deq;
   endrule

   rule reading(tlminff.first matches tagged Descriptor .d &&& d.command==READ);
      let r = tlminff.first;
      let n = noOfItems(d);
      let c = npiCommand(d);
      cmdFF.enq(tuple2(0, c)); // 0: No data items to be sent later
      readSizesFF.enq(n);
      skRspFF.enq(skeleton(d));
   endrule

   rule passWrData(tlminff.first matches tagged Data .*);
      let r = tlminff.first;
      tlminff.deq;
      wrDataFF.enq(npiWrArgs(r));
   endrule

   rule finishWr (skRspFF.first().command==WRITE);
      skRspFF.deq;
      endWr.deq;
      tlmoutff.enq(fleshOut(skRspFF.first(), ?, SUCCESS));
   endrule

   interface NPI_Port_Client npi;
     interface Get command;
	 method ActionValue#(NPICmd#(`TLM_TYPES)) get();
	    match {.items, .c} = cmdFF.first();
	    cmdFF.deq;
            if (items!=0)
	       wrDataCnt <= items;
	    else
	       endWr.enq(?);
	    return c;
	 endmethod
      endinterface
      interface Put readData;
	 method Action put(x);
	    let sk = skRspFF.first();
	    let newCnt = (rdDataCnt==0 ? readSizesFF.first() :
			  rdDataCnt - 1);
	    rdDataCnt <= newCnt;
		  tlmoutff.enq(tlmify(x,sk));
	    if (newCnt==0)
	       begin
		  skRspFF.deq;
		  readSizesFF.deq;
	       end
	 endmethod
      endinterface
      interface Get writeData;
	 method ActionValue#(NPIWrArgs#(`TLM_TYPES)) get() if (wrDataCnt>0);
	    let newCnt = wrDataCnt - 1;
	    wrDataCnt <= newCnt;
	    if (newCnt==0 &&& cmdBuf matches tagged Valid .c)
	       begin
		  cmdBuf <= tagged Invalid;
		  cmdFF.enq(tuple2(0, c)); // 0: No data items to be sent later
	       end
	    else
	       begin
		  endWr.enq(?);
	       end
	    let x = wrDataFF.first();
	    wrDataFF.deq;
	    return x;
	 endmethod
      endinterface
   endinterface

   interface TLMRecvIFC tlm;
      interface TLMRequest  rx = toPut(tlminff);
      interface TLMResponse tx = toGet(tlmoutff);
   endinterface
endmodule
   
endpackage

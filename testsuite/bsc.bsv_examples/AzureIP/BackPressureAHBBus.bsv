package BackPressureAHBBus;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import AHB::*;
import Connectable::*;
import FIFO::*;
import FShow::*;
import GetPut::*;
import Probe::*;
import Randomizable::*;
import TLM2::*;
import Vector::*;

`include "TLM.defines"

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module sysBackPressureAHBBus ();
   
   function Bool addrMatch0(AHBAddr#(`TLM_PRM) a);
      return (a[12] == 0);
   endfunction
   
   function Bool addrMatch1(AHBAddr#(`TLM_PRM) a);
      return (a[12] == 1);
   endfunction
   
   Reg#(Bit#(16)) count <- mkReg(0);
   
   TLMSendIFC#(`TLM_RR_STD) source_0 <- mkSource(tagged Invalid, True);
   TLMSendIFC#(`TLM_RR_STD) source_1 <- mkSource(tagged Invalid, True);
   
   AHBMasterXActor#(`TLM_RR_STD, `TLM_PRM_STD) master_0 <- mkAHBMasterStd;
   AHBMasterXActor#(`TLM_RR_STD, `TLM_PRM_STD) master_1 <- mkAHBMasterStd;
   AHBSlaveXActor#(`TLM_RR_STD, `TLM_PRM_STD)  slave_0  <- mkAHBSlaveStd(addrMatch0);
   AHBSlaveXActor#(`TLM_RR_STD, `TLM_PRM_STD)  slave_1  <- mkAHBSlaveStd(addrMatch1);
   
   TLMRecvIFC#(`TLM_RR_STD) mem_0 <- mkTLMRam_unbuffered(0,True);
   TLMRecvIFC#(`TLM_RR_STD) mem_1 <- mkTLMRam_unbuffered(1,True);
   
   Vector#(2, AHBFabricMaster#(`TLM_PRM_STD)) masters = newVector;
   Vector#(2, AHBFabricSlave#(`TLM_PRM_STD))  slaves = newVector;
   
   masters[0] = master_0.fabric;
   masters[1] = master_1.fabric;
   slaves[0]  = slave_0.fabric;
   slaves[1]  = slave_1.fabric;
   
   mkAHBBus(masters, slaves);

   mkConnection(source_0, master_0.tlm);
   mkConnection(source_1, master_1.tlm);
   mkConnection(slave_0.tlm, mem_0);
   mkConnection(slave_1.tlm, mem_1);
   
   rule every;
      count <= count + 1;
      if (count == 500) $finish;
   endrule
   
endmodule

   
(* synthesize *)
module mkSource#(Maybe#(TLMCommand) m_command, Bool verbose) (TLMSendIFC#(`TLM_RR_STD));
   
   Reg#(Bool)                initialized   <- mkReg(False);
   FIFO#(TLMResponseStd)     response_fifo <- mkFIFO;
   Randomize#(TLMRequestStd) gen           <- mkTLMRandomizer(m_command);
   Reg#(Bit#(2))             count         <- mkReg(0);                  
   
   rule every;
      count <= count + 1;
   endrule
   
   rule start (!initialized);
      gen.cntrl.init;
      initialized <= True;
   endrule
   
   rule grab_responses (count == 0);
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

endpackage

package AHBOneToOne;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import AHB::*;
import Connectable::*;
import TLM2::*;

`include "TLM.defines"

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module sysAHBOneToOne ();
   
   Reg#(Bit#(16)) count <- mkReg(0);
   
   TLMSendIFC#(`TLM_RR_STD) source <- mkTLM2Source(tagged Invalid, True);
   
   AHBMasterXActor#(`TLM_RR_STD, `TLM_PRM_STD) master <- mkAHBMasterStd;
   AHBSlaveXActor#(`TLM_RR_STD, `TLM_PRM_STD)  slave  <- mkAHBSlaveStd(alwaysAddrMatch);
   
   TLMRecvIFC#(`TLM_RR_STD) mem <-  mkTLMRam_unbuffered(0, True);

   mkConnection(source, master.tlm);
   mkConnection(master.fabric.bus, slave.fabric.bus);
   mkConnection(slave.tlm, mem);
   
   // AHBMonitor#(`TLM_PRM_STD) monitor <- mkAHBMonitor(False, master.fabric.bus, slave.fabric.bus);
   
   // a simple "arbiter" that gives the one master the grant whenever he asks for it.
   rule give_grant;
      master.fabric.arbiter.hGRANT(master.fabric.arbiter.hBUSREQ);
   endrule
   
   rule every;
      // always select the one slave
      slave.fabric.selector.select(True);
      count <= count + 1;
      if (count == 500) $finish;
   endrule
   
endmodule

endpackage

package AxiReadBus;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import Axi::*;
import Connectable::*;
import TLM2::*;
import Vector::*;

`include "Axi.defines"

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module sysAxiReadBus ();
   
   Reg#(Bit#(16)) count <- mkReg(0);
   
   function Bool addrMatch0(AxiAddr#(`TLM_PRM) a);
      return (a[12] == 0);
   endfunction
   
   function Bool addrMatch1(AxiAddr#(`TLM_PRM) a);
      return (a[12] == 1);
   endfunction
   
   TLMSendIFC#(`AXI_RR_STD)           source_0 <- mkTLMSource(tagged Valid READ, True);
   TLMSendIFC#(`AXI_RR_STD)           source_1 <- mkTLMSource(tagged Valid READ, True);
   
   AxiRdMasterXActorIFC#(`AXI_XTR_STD) master_0 <- mkAxiRdMasterStd;
   AxiRdMasterXActorIFC#(`AXI_XTR_STD) master_1 <- mkAxiRdMasterStd;

   AxiRdSlaveXActorIFC#(`AXI_XTR_STD)  slave_0 <- mkAxiRdSlaveStd(addrMatch0);
   AxiRdSlaveXActorIFC#(`AXI_XTR_STD)  slave_1 <- mkAxiRdSlaveStd(addrMatch1);
   
   TLMRecvIFC#(`AXI_RR_STD)  mem_0   <- mkTLMRam(0, True);
   TLMRecvIFC#(`AXI_RR_STD)  mem_1   <- mkTLMRam(1, True);

   mkConnection(source_0, master_0.tlm);
   mkConnection(source_1, master_1.tlm);
   
   Vector#(2, AxiRdFabricMaster#(`AXI_PRM_STD)) masters = newVector;
   Vector#(2, AxiRdFabricSlave#(`AXI_PRM_STD))  slaves = newVector;
   
   masters[0] = master_0.fabric;
   masters[1] = master_1.fabric;
   slaves[0]  = slave_0.fabric;
   slaves[1]  = slave_1.fabric;
   
   mkAxiRdBus(masters, slaves);
   
   mkConnection(slave_0.tlm, mem_0);
   mkConnection(slave_1.tlm, mem_1);
   
/* -----\/----- EXCLUDED -----\/-----
   let monitor_m0 <- mkMonitor(master_0.fabric.bus);
   let monitor_m1 <- mkMonitor(master_1.fabric.bus);
   let monitor_s0 <- mkMonitor(slave_0.fabric.bus);
   let monitor_s1 <- mkMonitor(slave_1.fabric.bus);
 -----/\----- EXCLUDED -----/\----- */
   
   rule every;
      count <= count + 1;
      if (count == 500) $finish;
   endrule
   
endmodule

endpackage

package DMAConfigRegs;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

import CBus::*;
import DMADefines::*;
import Vector::*;

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

interface ConfigRegs;
   interface Reg#(Bit#(8)) status;
   interface Vector#(NumChannels, Reg#(Bit#(1)))  active;
   interface Vector#(NumChannels, Reg#(Bit#(32))) descriptor;
endinterface

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

(* synthesize *)
module [Module] mkDMAConfigRegs(IWithCBus#(DCBus, ConfigRegs));
   let ifc <- exposeCBusIFC(mkDMAConfigRegsInternal);
   return ifc;
endmodule

module [DModWithCBus] mkDMAConfigRegsInternal (ConfigRegs);
   
   let icount = valueOf(NumChannels);
   
   Vector#(NumChannels, Reg#(Bit#(32))) desc_vector  = newVector;
   Vector#(NumChannels, Reg#(Bit#(1)))  active_vector = newVector;
   
   for (Integer i = 0; i < icount; i = i + 1)
      begin

	 let delta = DCAddr { a: (fromInteger(i) * 12'h020), o: 0};
   	 let descriptorAddr = descriptorAddrBase + delta;
	 let activeAddr     = activeAddrBase     + delta;
	 desc_vector[i]   <- mkCBRegRW(descriptorAddr, 0);
	 active_vector[i] <- mkCBRegRW(activeAddr,     0);
      end
   
   Reg#(Bit#(8)) reg_status   <- mkCBRegRW(statusAddr,   0);
   
   interface Reg status = reg_status;
   interface descriptor = desc_vector;
   interface active     = active_vector;

endmodule


////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

endpackage

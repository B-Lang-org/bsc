// Test the scheduling of modules from the library
// (that are not separately synthesized because they are polymorphic)

import SpecialFIFOs::*;
import FIFO::*;
import FIFOF::*;

(* synthesize *)
module mkBypassFIFO_Bit32 (FIFO#(Bit#(32)));
   (* hide *)
   FIFO#(Bit#(32)) _ifc <- mkBypassFIFO;
   return _ifc;
endmodule

(* synthesize *)
module mkBypassFIFOF_Bit32 (FIFOF#(Bit#(32)));
   (* hide *)
   FIFOF#(Bit#(32)) _ifc <- mkBypassFIFOF;
   return _ifc;
endmodule

// mkSizedBypassFIFOF is tested in TbBypassFIFO

// XXX Test mkBypassFIFOLevel


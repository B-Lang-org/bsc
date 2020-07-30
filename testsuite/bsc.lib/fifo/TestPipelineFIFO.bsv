// Test the scheduling of modules from the library
// (that are not separately synthesized because they are polymorphic)

import SpecialFIFOs::*;
import FIFO::*;
import FIFOF::*;

(* synthesize *)
module mkPipelineFIFO_Bit32 (FIFO#(Bit#(32)));
   (* hide *)
   FIFO#(Bit#(32)) _ifc <- mkPipelineFIFO;
   return _ifc;
endmodule

(* synthesize *)
module mkPipelineFIFOF_Bit32 (FIFOF#(Bit#(32)));
   (* hide *)
   FIFOF#(Bit#(32)) _ifc <- mkPipelineFIFOF;
   return _ifc;
endmodule


import Memory::*;
import MesaDefs::*;

(* synthesize *)
module mkLPMMemory(Memory#(SramAddr, SramData));
   let ifc <- mkMemoryLoad("SRAM.handbuilt", 0, 'h1fffff);
   return ifc;
endmodule

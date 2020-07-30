import Includes::*;
import Block2b::*;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
(* synthesize *)
module mkTb2b (Empty);
   LabIFC blockIFC();
   mkBlock2b iblock2b(blockIFC);
   Reg #(DataT) count <- mkReg(0);
   addRules( mkTestRules( blockIFC, count ) );
endmodule

import Includes::*;
import Block2::*;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
(* synthesize *)
module mkTb2 (Empty);
   LabIFC blockIFC();
   mkBlock2 iblock2(blockIFC);
   Reg #(DataT) count <- mkReg(0);
   addRules( mkTestRules( blockIFC, count ) );
endmodule

import Includes::*;
import Block1::*;

//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

// simple testbench hooking up Block1
(* synthesize *)
module mkTb1 (Empty);
   LabIFC blockIFC();
   mkBlock1 iblock1(blockIFC);
   Reg #(DataT) count <- mkReg(0);
   // add the common testbench rules to this block
   addRules( mkTestRules( blockIFC, count ) );
endmodule

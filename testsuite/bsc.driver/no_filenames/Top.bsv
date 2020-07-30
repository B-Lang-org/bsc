import Mid1::*;
import Mid2::*;

import "BVI" Banner =
   module mkBanner (Empty);
      default_clock no_clock; no_reset;
   endmodule

(* synthesize *)
module mkTop();
   if (genVerilog) Empty banner <- mkBanner();

   Empty mid1 <- mkMid1();
   Empty mid2 <- mkMid2();
endmodule

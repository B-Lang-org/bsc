import Mid1::*;
import Mid2::*;

(* synthesize *)
module mkTop();
   Empty mid1 <- mkMid1();
   Empty mid2 <- mkMid2();   
endmodule

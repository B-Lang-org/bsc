import Sub2::*;
import Sub3::*;

(* synthesize *)
module mkMid2();
   Empty sub2 <- mkSub2(100);
   Empty sub3 <- mkSub3();
endmodule: mkMid2
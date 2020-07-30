import Sub1::*;
import Sub2::*;

(* synthesize *)
module mkMid1();
   Empty sub1 <- mkSub1();
   Empty sub2 <- mkSub2(50);
endmodule: mkMid1
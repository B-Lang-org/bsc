import Vector::*;
import FixedPoint::*;

(* synthesize *)
module mkVectorStructUninitErr();
   Vector#(3, FixedPoint#(5,11)) fs;
   fs[0] = 0;
   
   rule test;
      $display(fs[1]);
      $finish(0);
   endrule
   
endmodule

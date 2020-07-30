import Vector::*;

(* synthesize *)
module sysVectorInBounds1();
   Integer x[4] = {1, 2, 3, 4};
   Vector#(4, Integer) v = arrayToVector(x);
   Integer y = v[1];
   
   rule test;
      $display("%0d", y);
      $finish(0);
   endrule
   
endmodule

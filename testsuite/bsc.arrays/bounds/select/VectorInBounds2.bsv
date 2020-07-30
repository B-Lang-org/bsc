import Vector::*;

(* synthesize *)
module sysVectorInBounds2();
   Integer x[4] = {1, 2, 3, 4};
   Vector#(4, Integer) v = arrayToVector(x);
   Bit#(2) ix = -2;
   Integer y = v[ix];
   
   rule test;
      $display("%0d", y);
      $finish(0);
   endrule
   
endmodule

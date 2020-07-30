import Vector::*;

(* synthesize *)
module mkMultiUninitErr1();
   Vector#(5,UInt#(32)) x;
   x[0] = 0;
   x[2] = 2;
   x[4] = 7;

   rule test;
     $display(x);
   endrule

endmodule

 

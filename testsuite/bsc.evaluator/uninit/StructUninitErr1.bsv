import Complex::*;

(* synthesize *)
module mkStructUninitErr1();
   Complex#(Int#(32)) foo;
   foo.rel = 0;   
   rule test;
      $display(foo);
      $finish(0);
   endrule
   
endmodule


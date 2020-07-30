import Complex::*;

(* synthesize *)
module sysStructUninitOK1();
   Complex#(Int#(32)) foo;
   foo.rel = 0;
   foo.img = -1;
   
   rule test;
      $display("%h", foo);
      $finish(0);
   endrule
   
endmodule


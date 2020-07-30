import Complex::*;

(* synthesize *)
module sysStructUninitOK2();
   Complex#(Int#(32)) foo;
   foo.img = -1;
   
   rule test;
      $display("%0d", foo.img);
      $finish(0);
   endrule
   
endmodule


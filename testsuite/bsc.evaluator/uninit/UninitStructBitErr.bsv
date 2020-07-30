import Complex::*;

(* synthesize *)
module sysUninitStructBitErr();
   Complex#(Bit#(6)) x;
   x.img = 0;
   for(Integer i = 0; i < 5; i = i + 1)
      x.rel[i] = pack(i % 3 == 0);
   
   rule test;
      $display("%0d", x);
      $display("(%0b, %0b)", x.rel, x.img);
      $finish(0);
   endrule
   
endmodule

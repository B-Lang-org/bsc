(* synthesize *)
module sysUninitBit1OK2();
   Bit#(1) x;
   x = 1;
   rule r;
      $display(x);
      $finish(0);
   endrule
endmodule

(* synthesize *)
module sysUninitBit1OK1();
   Bit#(1) x;
   x[0] = 1;
   rule r;
      $display(x);
      $finish(0);
   endrule
endmodule

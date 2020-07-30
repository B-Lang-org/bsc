(* synthesize *)
module sysUninitBit1Err1();
   Bit#(1) x;
   if (False)
      x = 0;
   rule r;
      $display(x);
      $finish(0);
   endrule
endmodule

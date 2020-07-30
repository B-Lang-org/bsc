(* synthesize *)
module sysUninitBitRangeUpdErr();
   Bit#(4) x;
   x[1:0] = 2'b11;
   //x[3:2] = 2'b11;
   rule r;
      $display(x);
      $finish(0);
   endrule
endmodule

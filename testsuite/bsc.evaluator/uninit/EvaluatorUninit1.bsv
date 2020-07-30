(* synthesize *)
module sysEvaluatorUninit1();
   Bool c = False;
   rule r;
      Bit#(4) x;
      if (c)
         x = 0;
      $display(x);
   endrule
endmodule

(* synthesize *)
module sysEvaluatorUninit2();
   Reg#(Bool) c <- mkReg(True);
   rule r;
      Bit#(4) x;
      if (c)
         x = 0;
      $display(x);
   endrule
endmodule

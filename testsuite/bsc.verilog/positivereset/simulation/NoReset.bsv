
(*synthesize*)
module sysNoReset();
   
   Reg#(UInt#(5)) foo <- mkReg(0, reset_by noReset);
   Reg#(UInt#(5)) c2 <- mkReg(0);
   
   rule update ;
      foo <= foo + 1;
      c2 <= c2 + 1;
      $display("update: %d %d", foo, c2);
   endrule
   
   rule fine (foo == maxBound || c2 == maxBound) ;
      $display("finish: %d %d", foo, c2);
      $finish(0);
   endrule
   
endmodule

(* synthesize *)
module sysBitExtractOutOfRangeHigh();
   Reg#(Bit#(64)) r <- mkReg(64'hDEADBEEFBAADF00D);
   
   rule test;
      $display("%h", r[96:32]);
      $finish(0);
   endrule
   
endmodule

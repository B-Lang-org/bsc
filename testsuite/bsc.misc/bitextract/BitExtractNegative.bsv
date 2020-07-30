(* synthesize *)
module sysBitExtractNegative();
   Reg#(Bit#(64)) r <- mkReg(64'hDEADBEEFBAADF00D);
   
   rule test;
      $display("%h", r[32:47]);
      $finish(0);
   endrule
   
endmodule

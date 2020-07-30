(* synthesize *)
module sysBitExtractZero();
   Reg#(Bit#(64)) r <- mkReg(64'hDEADBEEFBAADF00D);
   
   rule test;
      $display("%h", r[32:33]);
      $finish(0);
   endrule
   
endmodule

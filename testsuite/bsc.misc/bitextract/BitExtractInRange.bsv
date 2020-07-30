(* synthesize *)
module sysBitExtractInRange();
   Reg#(Bit#(64)) r <- mkReg(64'hDEADBEEFBAADF00D);
   
   rule test;
      $display("%h", r[47:32]);
      $finish(0);
   endrule
   
endmodule

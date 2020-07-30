(* synthesize *)
module sysBitUpdateOutOfRangeLow();
   Reg#(Bit#(64)) r <- mkReg(64'hDEADBEEFBAADF00D);
   
   Reg#(Bool) updated <- mkReg(False);
   
   rule update(!updated);
      r[47:-32] <= 0;
      updated <= True;
   endrule
   
   rule test(updated);
      $display("%h", r);
      $finish(0);
   endrule
   
endmodule

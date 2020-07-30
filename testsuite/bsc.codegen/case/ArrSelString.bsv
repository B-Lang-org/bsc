(* synthesize *)
module sysArrSelString();
   Reg#(Bit#(2)) rg <- mkReg(1);
   String ss[4] = { "zero", "one", "two", "three" };
   rule r;
      $display(ss[rg]);
   endrule
endmodule

(* synthesize *)
module sysTest();
   Reg#(Bit#(256)) rg1 <- mkReg(0);
   Reg#(Bit#(256)) rg2 <- mkReg(0);
   Reg#(Bit#(512)) rg3 <- mkReg(0);

   rule r1 ({rg1,rg2} == rg3);
      $display("hi");
      $finish(0);
   endrule
endmodule

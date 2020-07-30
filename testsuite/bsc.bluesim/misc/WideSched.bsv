// Test wide operators in scheduling
// (here, concat in a rule predicate)

(* synthesize *)
module sysWideSched();
   Reg#(Bit#(256)) rg1 <- mkReg('1);
   Reg#(Bit#(256)) rg2 <- mkReg('1);
   Reg#(Bit#(512)) rg3 <- mkReg('1);

   rule r1 ({rg1,rg2} == rg3);
      $display("hi");
      $finish(0);
   endrule
endmodule

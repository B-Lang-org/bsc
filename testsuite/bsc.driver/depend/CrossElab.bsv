// A module whose elaboration differs by backend (via genVerilog), so its
// .ba file records the backend it was elaborated for
(* synthesize *)
module sysCrossElab();
   Reg#(Bit#(8)) rg <- mkReg(genVerilog ? 1 : 0);
   rule r;
      $display("val %0d", rg);
      $finish(0);
   endrule
endmodule

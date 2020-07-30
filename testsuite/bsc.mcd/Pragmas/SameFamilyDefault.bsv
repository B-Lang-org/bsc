interface TestIfc;
  // empty
endinterface

(* synthesize,
   clock_family = "default_clock, c2"
 *)
module mkTest(Clock c2, TestIfc ifc);

  Reg#(Bool) x1 <- mkReg(False);

  Reg#(Bool) x2 <- mkReg(True, clocked_by c2, reset_by noReset);

  rule r;
    x1 <= x2;
    x2 <= x1;
  endrule

endmodule

(* synthesize *)
module sysSameFamilyDefault();

  Clock clk2 <- exposeCurrentClock;

  TestIfc test <- mkTest(clk2);

endmodule
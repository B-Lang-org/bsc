interface TestIfc;
  // empty
endinterface

// This should generate an error because there is no c2 clock input
(* synthesize,
   clock_family = "c1, c2"
 *)
module mkTest(Clock c1, Reset rst1, TestIfc ifc);

  Reg#(Bool) x1 <- mkReg(False, clocked_by c1, reset_by rst1);

  rule r;
    x1 <= !x1;
  endrule

endmodule

(* synthesize *)
module sysSameFamilyBoundary();

  Clock clk <- exposeCurrentClock;
  Reset rst <- exposeCurrentReset;

  TestIfc test <- mkTest(clk, rst);

endmodule
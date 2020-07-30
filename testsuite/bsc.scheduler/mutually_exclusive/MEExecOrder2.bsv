// two rules that are mutually exclusive 
// should still be that way with exec order
// check that it works even if we lie with the annotation
(* synthesize *)
module sysMEExecOrder2();

  Reg#(Bit#(17)) r <- mkReg(99);
  
  // this register is here so that the differences in 
  // Verilog and Bluesim reset handling don't let 
  // the exit rule fire during reset in Bluesim but not Verilog
  Reg#(Bool) done <- mkReg(True);

  (* mutually_exclusive="rule1, rule2" *)
  (* execution_order="rule1, rule2, exit" *)
  rule rule1(r > 1);
    r <= r + 1;
    $display("rule1");
  endrule

  rule rule2(r > 2);
    r <= r + 2;
    $display("rule2");
  endrule

  rule exit(done);
    $display("exit");
    $finish(0);
  endrule

endmodule
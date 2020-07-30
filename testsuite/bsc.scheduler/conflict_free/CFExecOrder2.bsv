(* synthesize *)
module sysCFExecOrder2();
 
  Reg#(Bit#(12)) r <- mkReg(0);
  Reg#(Bool) done <- mkReg(True);

  (* execution_order = "b,a,c" *)
  rule a;
   $display("a");
   r <= 1;
  endrule

  (* conflict_free = "a,b" *)
  rule b;
   $display("b: %0d", r);
  endrule

  rule c(done);
   $finish(0);
  endrule

endmodule

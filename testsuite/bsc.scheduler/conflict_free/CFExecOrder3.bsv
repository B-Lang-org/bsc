(* synthesize *)
module sysCFExecOrder3();

  Reg#(Bit#(5))  r <- mkReg(0);
  Reg#(Bit#(16)) s <- mkReg(0);

  (* execution_order = "c, b, a" *)
  (* conflict_free = "a,b" *)
  rule b;
    $display("b");
    if (r == 1) r <= r + 2;
    s <= 7;
  endrule

  rule a;
    $display("a");
    if (r == 0) r <= r + 1;
    s <= 5;
  endrule

  rule c;
    $display("s %0d", s);
    if (r == 3) $finish(0);
  endrule

endmodule

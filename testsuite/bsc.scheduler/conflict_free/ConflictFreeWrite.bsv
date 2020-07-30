(* synthesize *)
module sysConflictFreeWrite();

  Reg#(Bit#(17)) y <- mkReg(0);

  (* conflict_free = "r1, r2" *)
  rule r1;
    if (y == 0) y <= 1;
  endrule

  rule r2;
    if (y == 1) y <= 2;
  endrule

  rule exit;
    $display("y: %0d", y);
    if (y == 2) $finish(0);
  endrule

endmodule

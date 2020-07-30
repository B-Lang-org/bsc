(* synthesize *)
module sysDumpFlushTest(Empty);
  Reg#(UInt#(32)) r();
  mkReg#(0) ther(r);
  Reg#(UInt#(16)) c();
  mkReg#(0) thec(c);
  rule ralways
  (True); c <= c + 1;
  endrule
  rule r1
  (c == 1); $dumpoff;
  endrule
  rule r2
  (c == 2); r <= zeroExtend(c);
  endrule
  rule r3
  (c == 3); r <= r + 1;
  endrule
  rule r4
  (c == 4); $dumpon;
  endrule
  rule r5
  (c == 5); r <= zeroExtend(c + truncate(r));
  endrule
  rule r6
  (r == 6); $dumpoff;
  endrule
  rule r7
  (c == 7); $dumpflush; $finish(0);
  endrule
  rule r8
  (True); $dumpvars;
  endrule
endmodule

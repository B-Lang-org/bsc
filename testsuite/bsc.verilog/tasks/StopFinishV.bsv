export sysStopFinishV;
module sysStopFinishV(Empty);
  Reg#(Bit#(16)) r();
  mkReg#(0) the_r(r);
  rule r1
   (r == 0); $finish(0);
  endrule: r1
  rule r2
   (r == 1); $finish(1);
  endrule: r2
  rule r3
   (r == 2); $finish(2);
  endrule: r3
  rule r4
   (r == 3); $finish();
  endrule: r4
  rule r5
   (r == 4); $stop(0);
  endrule: r5
  rule r6
   (r == 5); $stop(1);
  endrule: r6
  rule r7
   (r == 6); $stop(2);
  endrule: r7
  rule r8
   (r == 7); $stop();
  endrule: r8
endmodule: sysStopFinishV


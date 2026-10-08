// R2 trigger: system-task foreign blocks with shared def closures
(* synthesize *)
module sysStableTasks();
   Reg#(UInt#(16)) x <- mkReg(0);
   Reg#(UInt#(16)) y <- mkReg(1);
   rule tick;
      let s = x + y;
      let p = x * y;
      $display("s=%0d", s);
      $display("p=%0d", p);
      $write("x=%0d y=%0d", x, y);
      x <= s; y <= p;
      if (x > 100) $finish(0);
   endrule
endmodule

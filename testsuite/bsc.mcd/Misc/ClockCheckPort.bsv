import Clocks::*;

(* synthesize *)
module mkSub(Bit#(16) x, Empty ifc);
  rule go;
    $display("x: %0d", x);
  endrule
endmodule

(* synthesize *)
module sysClockCheckPort(Empty);

  Clock c1 <- mkAbsoluteClock(0, 32);

  Reg#(Bit#(16)) a();
  mkReg#(17) the_a(a, clocked_by c1, reset_by noReset);

  Reg#(Bit#(16)) b();
  mkReg#(23) the_b(b);

  Empty sub <- mkSub(a+b);

endmodule 

import Clocks::*;

interface Test;
  method Action m1;
  method Bool m2;
  interface Clock c;
  interface Reset r;
endinterface

(* synthesize *)
module mkMultBoundaryClockErr(Test);

  Clock c_int <- mkAbsoluteClock(0,17);

  Clock c2 <- mkAbsoluteClock(10, 23);
  Reset r2 <- mkInitialReset(3, clocked_by c2);

  Reg#(Bool) b <- mkReg(False, clocked_by c_int);
    
  method m1 = b._write(True);
  method m2 = b;

  interface c = when(b, c2);
  interface r = when(b, r2);

endmodule

  

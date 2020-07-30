import Vector::*;
import Clocks::*;

(* synthesize *)
module sysClockedByPort();
    Clock c <- mkAbsoluteClock(15,15);
    Reset r <- mkInitialReset(2, clocked_by c);

    Reg#(Vector#(3,int)) rg <- mkReg(cons(17,cons(42,cons(2,nil))),
                                     clocked_by c, reset_by r);

    Empty e <- mkClockedByPort_Sub(c,r,rg);
endmodule

(* synthesize *)
module mkClockedByPort_Sub (Clock c, Reset r,
                            (* clocked_by="c", reset_by="r" *)
                            Vector#(3,int) vec,
                            Empty ifc);

    Reg#(Bool) done <- mkReg(False, clocked_by c, reset_by r);

    rule disp (!done);
      $display("%d %d %d", vec[0], vec[1], vec[2]);
      done <= True;
    endrule

    rule do_finish (done);
      $finish(0);
    endrule

endmodule


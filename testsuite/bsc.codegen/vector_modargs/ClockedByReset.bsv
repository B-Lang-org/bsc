import Vector::*;
import Clocks::*;

(* synthesize *)
module sysClockedByReset();
    Clock c <- mkAbsoluteClock(15,15);

    Reset rst0 <- mkInitialReset(2, clocked_by c);
    Reset rst1 <- mkInitialReset(4, clocked_by c);
    Reset rst2 <- mkInitialReset(6, clocked_by c);
    Vector#(3,Reset) rs = cons(rst0, cons(rst1, cons(rst2, nil)));

    SubIfc i <- mkClockedByReset_Sub(c,rs);

    rule r0 (i.rg[0]);
	$display("rg[0]");
	i.rg[0] <= False;
    endrule

    rule r1 (i.rg[1]);
	$display("rg[1]");
	i.rg[1] <= False;
    endrule

    rule r2 (i.rg[2]);
	$display("rg[2]");
	i.rg[2] <= False;
    endrule

    rule do_finish (!i.rg[2]);
        $finish(0);
    endrule
endmodule

interface SubIfc;
    interface Vector#(3,Reg#(Bool)) rg;
endinterface

(* synthesize *)
module mkClockedByReset_Sub (Clock c,
                             (* clocked_by="c" *)
                             Vector#(3,Reset) rs,
                             SubIfc ifc);

    Reg#(Bool) rg0 <- mkReg(True, clocked_by c, reset_by rs[0]);
    Reg#(Bool) rg1 <- mkReg(True, clocked_by c, reset_by rs[1]);
    Reg#(Bool) rg2 <- mkReg(True, clocked_by c, reset_by rs[2]);

    interface rg = cons(rg0, cons(rg1, cons(rg2, nil)));
endmodule


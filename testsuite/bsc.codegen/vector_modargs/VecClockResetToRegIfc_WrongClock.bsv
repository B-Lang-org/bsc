import Vector::*;
import Clocks::*;

// Test that a Vector of clocks and resets can be sent to a submodule
// to clock registers which are exposed in the module's interface,
// whose methods get the appropriate clocks and can be used on those
// clocks in the parent.

(* synthesize *)
module sysVecClockResetToRegIfc_WrongClock ();
    Vector#(4,Clock) clks = ?;
    Vector#(4,Reset) rsts = ?;

    clks[0] <- mkAbsoluteClock(10,10);
    rsts[0] <- mkInitialReset(2, clocked_by clks[0]);

    clks[1] <- mkAbsoluteClock(15,15);
    rsts[1] <- mkInitialReset(2, clocked_by clks[1]);

    clks[2] <- mkAbsoluteClock(20,20);
    rsts[2] <- mkInitialReset(2, clocked_by clks[2]);

    clks[3] <- mkAbsoluteClock(25,25);
    rsts[3] <- mkInitialReset(2, clocked_by clks[3]);

    SubIfc sub <- mkVecClockResetToRegIfc_Sub(clks,rsts);

    for (Integer i=0; i<4; i=i+1) begin
        Reg#(int) rg <- mkReg(0, clocked_by clks[i], reset_by rsts[i]);
        Integer j = 3-i;
        rule incr_reg;
           if (sub.bs[j]) begin
              rg <= rg + 1;
              $display("incrementing %h", i);
              sub.bs[j] <= False;
           end else begin
              $display("not incrementing %h", i);
              sub.bs[j] <= True;
           end
           if (rg > 10)
             $finish(0);
        endrule
    end
endmodule

interface SubIfc;
    interface Vector#(4,Reg#(Bool)) bs;
endinterface

(* synthesize *)
module mkVecClockResetToRegIfc_Sub #(Vector#(4,Clock) clks,
                                     Vector#(4,Reset) rsts)
                                    (SubIfc);
    Vector#(4,Reg#(Bool)) outs = ?;
    for (Integer i=0; i<4; i=i+1) begin
	Reg#(Bool) rg <- mkRegU(clocked_by clks[i]);
	outs[i] = rg;
    end
    interface bs = outs;
endmodule


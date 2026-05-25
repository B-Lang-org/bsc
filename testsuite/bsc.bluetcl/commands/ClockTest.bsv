package ClockTest;

import Clocks::*;

// ---- Module that EXPORTS a clock and a reset via its interface -----
// Exercises wiretypemap's output-clock / output-reset paths.

interface ClockOutIfc;
    interface Clock  newClk;
    interface Reset  newRst;
    method   Bool    enabled;
endinterface

(* synthesize *)
module mkClockOut (ClockOutIfc);
    Reg#(Bool)         en <- mkReg(True);
    GatedClockIfc      gc <- mkGatedClockFromCC(True);
    MakeResetIfc       mr <- mkReset(2, True, gc.new_clk);
    interface newClk   = gc.new_clk;
    interface newRst   = mr.new_rst;
    method   enabled   = en;
endmodule

// Coverage notes on gate signals across the test fixture:
//   * Input clock WITHOUT gate:   mkArgClock's argument altClk
//                                 -> wire CLK_altClk only
//   * Input clock WITH gate:      gc.CLK_IN + gc.CLK_GATE_IN (the
//                                 gated-clock submodule's clock input)
//   * Output clock WITH gate:     mkClockOut's newClk
//                                 -> CLK_newClk + CLK_GATE_newClk
//   * Output clock WITHOUT gate:  not exercised. bsc always emits a
//                                 CLK_GATE_<name> port for exposed
//                                 output clocks even when the gate is
//                                 structurally a constant; the framework
//                                 has no source-level way to suppress
//                                 the gate port entirely.
// All four code branches in getWireTypeMap (Right/Left for input
// clocks, Just/Nothing for output clocks) are still covered: the
// submodule clock walk visits both "Left _" and "Right vn" cases.

// ---- Module that TAKES clock and reset as explicit arguments -------
// Exercises wiretypemap's argument-clock handling (these become extra
// input_clocks entries on mkArgClock's apkg_external_wires).

interface ArgClockIfc;
    method Action  feed(Bit#(16) v);
    method Bit#(16) lastDefault();
    method Bit#(16) lastAlt();
endinterface

(* synthesize *)
module mkArgClock #(Clock altClk, Reset altRst) (ArgClockIfc);
    Reg#(Bit#(16))  defReg <- mkReg(0);
    Reg#(Bit#(16))  altReg <- mkReg(0, clocked_by altClk, reset_by altRst);
    SyncFIFOIfc#(Bit#(16)) toAlt <- mkSyncFIFOToCC(2, altClk, altRst);
    // Note: SyncFIFOToCC means "from arbitrary clock TO current clock"
    // -- so the input side is on altClk, output on the default clock.
    rule drain (toAlt.notEmpty); toAlt.deq; endrule
    method Action feed (Bit#(16) v);
        defReg <= v;
    endmethod
    method lastDefault = defReg;
    method lastAlt     = altReg;
endmodule

// ---- Top-level that wires them together ----------------------------

(* synthesize *)
module mkClockTest (Empty);
    ClockOutIfc      maker <- mkClockOut;
    ArgClockIfc      taker <- mkArgClock(maker.newClk, maker.newRst);
    Reg#(Bit#(8))    cnt   <- mkReg(0);
    rule tick;
        cnt <= cnt + 1;
        taker.feed(extend(cnt));
    endrule
endmodule

endpackage

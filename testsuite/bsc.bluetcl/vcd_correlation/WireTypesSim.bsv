package WireTypesSim;

import Vector::*;
import FIFOF::*;
import WireTypes::*;

// Top-level simulation wrapper around mkWireTypes that exercises every
// method, dumps a VCD, and finishes deterministically. Used by the
// VCD correlation test.

(* synthesize *)
module sysWireTypeTest (Empty);
    WireTypeIfc            dut <- mkWireTypes;
    Reg#(UInt#(8))         cnt <- mkReg(0);
    Reg#(Bool)             vcd_started <- mkReg(False);

    rule start_vcd (!vcd_started);
        $dumpvars;
        vcd_started <= True;
    endrule

    rule tick (vcd_started);
        cnt <= cnt + 1;
    endrule

    rule exercise_loadPixel (cnt == 1);
        dut.loadPixel(Pixel { x: 7, y: 11, color: BLUE });
    endrule

    rule exercise_setPalette (cnt == 3);
        Vector#(4, Color) p = newVector;
        p[0] = RED;
        p[1] = GREEN;
        p[2] = BLUE;
        p[3] = RED;
        dut.setPalette(p);
    endrule

    rule observe (cnt == 5);
        let p   = dut.topPixel;
        let mp  = dut.maybePixel;
        let pal = dut.palette;
        let cl  = dut.currentCell;
        $display("topPixel = (%0d,%0d)", p.x, p.y);
        $display("maybePixel isJust = %b", isValid(mp));
        $display("palette[0] = ", fshow(pal[0]));
        $display("currentCell = ", fshow(cl));
    endrule

    rule finish (cnt == 8);
        $finish;
    endrule
endmodule

endpackage

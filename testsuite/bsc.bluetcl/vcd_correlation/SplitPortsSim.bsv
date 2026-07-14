package SplitPortsSim;

import SplitPorts::*;
import SplitPortsTest::*;

// Simulation wrapper that exercises mkSplitPortsTest so its ports and
// internal state appear in the VCD. The DeepSplit-collapsed
// sub-interface arguments (`sub.put` taking `DeepSplit Inner`,
// `sub.putHdr` taking `DeepSplit Header`) are the wires we most want
// to see correlated, plus the registers and FIFOF carrying Inner /
// Header / Bit#(16) -- those land in the Bluesim VCD.

(* synthesize *)
module sysSplitPortsTest (Empty);
    Outer                dut <- mkSplitPortsTest;
    Reg#(UInt#(8))       cnt <- mkReg(0);
    Reg#(Bool)           started <- mkReg(False);

    rule start (!started);
        $dumpvars;
        started <= True;
    endrule

    rule tick (started);
        cnt <= cnt + 1;
    endrule

    rule drive_inner (cnt == 1);
        dut.sub.put(DeepSplit(Inner { tag: 4'h7, payload: 12'hABC }));
    endrule

    rule drive_header (cnt == 2);
        dut.sub.putHdr(DeepSplit(Header { src: 8'h12, dst: 8'h34, flags: 4'b1010 }));
    endrule

    rule observe (cnt == 4);
        let v = dut.sub.get;
        let h = dut.sub.getHdr;
        let c = dut.sub.count;
        $display("sub.get  = %h:%h",   v.tag, v.payload);
        $display("sub.getHdr = %h/%h/%b", h.src, h.dst, h.flags);
        $display("sub.count = %0d", c);
    endrule

    rule bump (cnt == 6);
        dut.bump;
    endrule

    rule finish (cnt == 10);
        $finish;
    endrule
endmodule

endpackage

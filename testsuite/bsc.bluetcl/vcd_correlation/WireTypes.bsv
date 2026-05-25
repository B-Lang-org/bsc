package WireTypes;

import Vector::*;
import FIFOF::*;
import BRAM::*;
import Clocks::*;
import Probe::*;

// ---- Interesting type fixtures ----------------------------------

typedef enum { RED, GREEN, BLUE } Color
    deriving (Bits, Eq, FShow);

typedef struct {
    UInt#(8) x;
    UInt#(8) y;
    Color    color;
} Pixel deriving (Bits, Eq, FShow);

typedef union tagged {
    Pixel    Px;
    UInt#(16) Idx;
    void     Empty;
} Cell deriving (Bits, Eq, FShow);

typedef Vector#(4, Color) ColorPalette;

// ---- A module that exercises rich port types --------------------

interface WireTypeIfc;
    method Action          loadPixel    (Pixel p);
    method Pixel           topPixel     ();
    method Maybe#(Pixel)   maybePixel   ();
    method Action          setPalette   (ColorPalette cs);
    method ColorPalette    palette      ();
    method Cell            currentCell  ();
endinterface

// ---- A separately-synthesized leaf module --------------------------
// Used by mkWireTypes below. Instantiating it twice creates two
// distinct sub-scopes (leafA, leafB) in the VCDs -- each correlates
// against the *same* mkPixelStash wiretypemap. This proves the per-
// module map design works: one wiretypemap query covers all
// instances of that module.

interface PixelStash;
    method Action push(Pixel p);
    method Pixel  top();
    method Bit#(8) depth();
endinterface

(* synthesize *)
module mkPixelStash (PixelStash);
    Reg#(Pixel)    last  <- mkReg(Pixel { x: 0, y: 0, color: RED });
    FIFOF#(Pixel)  q     <- mkFIFOF;
    Reg#(Bit#(8))  cnt   <- mkReg(0);

    rule sink (q.notEmpty);
        last <= q.first;
        q.deq;
        cnt  <= cnt + 1;
    endrule

    method Action push(Pixel p) = q.enq(p);
    method Pixel  top  = last;
    method Bit#(8) depth = cnt;
endmodule

(* synthesize *)
module mkWireTypes (WireTypeIfc);
    // Registers with rich element types
    Reg#(Pixel)             px  <- mkReg(Pixel { x: 0, y: 0, color: RED });
    Reg#(Maybe#(Pixel))     mpx <- mkReg(tagged Invalid);
    Reg#(ColorPalette)      pal <- mkReg(replicate(GREEN));
    Reg#(Cell)              cl  <- mkReg(tagged Empty);

    // A small FIFOF of a tagged union, so we get a submodule with
    // an interesting element type on its input/output ports
    FIFOF#(Cell)            cells <- mkFIFOF;

    // CReg (concurrent register) with all 5 ports, carrying a rich
    // type. Exercises the CReg → Reg port-rename path in getWireTypeMap:
    // bluetcl sees the pre-aInlineCReg AVInst with port names like
    // cregDIN_0/cregQOUT_0, but the actual Verilog wires after
    // inlining are D_IN_0..D_IN_4/Q_OUT_0..Q_OUT_4. getWireTypeMap
    // emits both candidate forms so a VCD correlator matches whichever
    // the build settled on.
    Reg#(Pixel) creg[5] <- mkCReg(5, Pixel { x: 0, y: 0, color: GREEN });

    // RWire carrying a tagged-union (Cell). After aInlineWires, the
    // AVInst goes away and the surviving wires are `cellWire$wget`
    // (Cell-typed) and `cellWire$whas` (Bool). getWireTypeMap emits
    // both forms so a VCD correlator picks them up regardless of
    // whether the wire was inlined.
    RWire#(Cell)            cellWire <- mkRWire;
    // BypassWire (always-on) carrying a Maybe-of-struct. After
    // inlining, only `pixelBypass$wget` survives (Maybe#(Pixel)-typed;
    // BypassWires don't have a whas signal since it's always 1).
    Wire#(Maybe#(Pixel))    pixelBypass <- mkBypassWire;
    // PulseWire is just an RWire0 wrapper (zero-width data). The
    // wiretypemap emits candidates `pulse$whas` / `pulse.whas` (Bool)
    // since RWire0 has no wget. Whether the literal pulse$whas wire
    // survives in the synthesized Verilog VCD depends on the
    // optimizer -- with the two consumers below (counter + shift
    // register) the value typically gets folded into the consumer
    // expressions rather than kept as a named shared wire. The
    // downstream `pulseCount` / `pulseHistory` registers always show
    // up in the VCD with their proper types and correlate cleanly.
    PulseWire               pulse        <- mkPulseWire;
    Reg#(UInt#(8))          pulseCount   <- mkReg(0);
    Reg#(Bit#(8))           pulseHistory <- mkReg(0);
    Reg#(Bit#(2))           pulseTick    <- mkReg(0);

    // A second PulseWire used with a simple, single-consumer pattern
    // -- aOpt aggressively folds `simplePulse._read` into the rule
    // predicate, eliminating the literal `simplePulse$whas` wire from
    // the Verilog VCD. With `-keep-inlined-boundaries`, the wire is
    // preserved. This is a deliberate negative-then-positive test of
    // the flag's effect.
    PulseWire               simplePulse  <- mkPulseWire;
    Reg#(UInt#(4))          simpleCount  <- mkReg(0);

    // Two instances of a separately-synthesized leaf, so the VCD has
    // sub-scopes `leafA` and `leafB` (each instantiating a Reg#(Pixel)
    // and a FIFOF#(Pixel)). The same mkPixelStash wiretypemap covers
    // both sub-scopes -- the hierarchical correlation test exercises
    // this.
    PixelStash              leafA <- mkPixelStash;
    PixelStash              leafB <- mkPixelStash;

    // Probe primitives -- specifically for VCD inspection. Bluesim
    // dumps them as `<inst>$PROBE`; Verilog instantiates ProbeWire
    // with an IN port (covered by the standard candidate path).
    Probe#(Pixel)           pxProbe   <- mkProbe;
    Probe#(Maybe#(Pixel))   mpxProbe  <- mkProbe;

    // BRAM with a tagged-union data type (polymorphic primitive: addr +
    // data, both interesting). Address type is Bit#(6) -> 64 entries.
    BRAM_Configure cfg = defaultValue;
    cfg.memorySize = 64;
    BRAM1Port#(Bit#(6), Cell) bram <- mkBRAM1Server(cfg);

    // SyncFIFO crossing clock domains, carrying a Maybe of struct.
    // Polymorphic primitive with typed ports on both clock sides.
    Clock fastClk <- exposeCurrentClock;
    Reset fastRst <- exposeCurrentReset;
    SyncFIFOIfc#(Maybe#(Pixel)) syncfifo <- mkSyncFIFO(2, fastClk, fastRst, fastClk);

    rule rotate_palette;
        ColorPalette p = pal;
        Color first = p[0];
        for (Integer i = 0; i < 3; i = i + 1) p[i] = p[i+1];
        p[3] = first;
        pal <= p;
    endrule

    rule sink_cells (cells.notEmpty);
        cl <= cells.first;
        cells.deq;
    endrule

    rule drain_sync (syncfifo.notEmpty);
        syncfifo.deq;
    endrule

    // Exercise each CReg port from a separate rule so all five ports
    // get used in the synthesized output (otherwise unused ports may
    // be optimized away). This is the canonical CReg use pattern.
    rule poke_creg_0; creg[0] <= Pixel { x: 1, y: 1, color: BLUE  }; endrule
    rule poke_creg_1; creg[1] <= Pixel { x: 2, y: 2, color: RED   }; endrule
    rule poke_creg_2; creg[2] <= Pixel { x: 3, y: 3, color: GREEN }; endrule
    rule poke_creg_3; creg[3] <= Pixel { x: 4, y: 4, color: BLUE  }; endrule
    rule poke_creg_4; creg[4] <= Pixel { x: 5, y: 5, color: RED   }; endrule

    rule poke_cell_wire;
        cellWire.wset(tagged Px (Pixel { x: 9, y: 9, color: RED }));
    endrule

    rule poke_bypass;
        pixelBypass <= tagged Valid (Pixel { x: 11, y: 11, color: BLUE });
    endrule

    rule advance_pulse_tick;
        pulseTick <= pulseTick + 1;
    endrule

    // Send pulse on a non-trivial condition. Two reasons for the
    // complexity:
    //   * If pulse were sent every cycle, aOpt would fold pulse._read
    //     to constant True and eliminate it.
    //   * If the predicate were a single 1-bit comparison, aOpt would
    //     inline it at each use site instead of sharing a wire.
    // A multi-term predicate is complex enough that aOpt prefers to
    // share the result as a named def -- which after aInlineWires
    // becomes the `pulse$whas` wire visible in the Verilog VCD.
    rule poke_pulse ((pulseTick == 0 || pulseTick == 2)
                     && pack(pulseCount)[0] == 0 && pulseHistory[7] == 0);
        pulse.send;
    endrule

    // Two separate consumers of pulse._read in two separate rules.
    // Each rule's guard or body references pulse, forcing bsc to
    // compute pulse._read (= pulse$whas) once and share the wire.
    rule count_pulse (pulse);
        pulseCount <= pulseCount + 1;
    endrule

    rule shift_history;
        pulseHistory <= { pulseHistory[6:0], pack(pulse) };
    endrule

    // Drive simplePulse unconditionally and consume in exactly one
    // rule with a trivial predicate -- the canonical pattern that aOpt
    // folds away. Without -keep-inlined-boundaries: simplePulse$whas
    // disappears from the Verilog VCD. With the flag: it survives.
    rule poke_simple;
        simplePulse.send;
    endrule
    rule count_simple (simplePulse);
        simpleCount <= simpleCount + 1;
    endrule

    method Action loadPixel (Pixel p);
        px <= p;
        mpx <= tagged Valid p;
        cells.enq(tagged Px p);
        syncfifo.enq(tagged Valid p);
        bram.portA.request.put(BRAMRequest{
            write: True, responseOnWrite: False,
            address: truncate(pack(p.x)), datain: tagged Px p });
        leafA.push(p);
        leafB.push(Pixel { x: p.x + 1, y: p.y, color: p.color });
        pxProbe  <= p;
        mpxProbe <= tagged Valid p;
    endmethod

    method Pixel         topPixel    () = px;
    method Maybe#(Pixel) maybePixel  () = mpx;

    method Action setPalette (ColorPalette cs);
        pal <= cs;
    endmethod

    method ColorPalette palette     () = pal;
    method Cell         currentCell () = cl;
endmodule

endpackage

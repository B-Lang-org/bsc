package WireTypes;

import Vector::*;
import FIFOF::*;
import BRAM::*;
import Clocks::*;

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

    method Action loadPixel (Pixel p);
        px <= p;
        mpx <= tagged Valid p;
        cells.enq(tagged Px p);
        syncfifo.enq(tagged Valid p);
        bram.portA.request.put(BRAMRequest{
            write: True, responseOnWrite: False,
            address: truncate(pack(p.x)), datain: tagged Px p });
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

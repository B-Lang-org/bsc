package CoercionTypes;

typedef struct {
    Bit#(4) upper;
    Bit#(4) lower;
} Nibbles deriving (Bits, Eq, FShow);

typedef struct {
    Bit#(3) tag;
    Bit#(5) payload;
} TaggedPayload deriving (Bits, Eq, FShow);

interface CseTypes;
    method Action load(Bit#(8) a, Bit#(8) b);
    method Nibbles nibbles;
    method TaggedPayload taggedPayload;
endinterface

// Two separately written expressions enter different nominal types. Their
// downstream representation is identical, making the shared expression a
// useful test that source-type evidence must be a set.
(* synthesize *)
module mkCseTypes(CseTypes);
    Reg#(Bit#(8)) x <- mkReg(0);
    Reg#(Bit#(8)) y <- mkReg(0);
    Reg#(Nibbles) ns <- mkReg(unpack(0));
    Reg#(TaggedPayload) ts <- mkReg(unpack(0));
    rule update;
        Bit#(8) forNibbles = (x + y) ^ 8'h53;
        Bit#(8) forTagged = (x + y) ^ 8'h53;
        Nibbles nv = unpack(forNibbles);
        TaggedPayload tv = unpack(forTagged);
        ns <= nv;
        ts <= tv;
    endrule
    method Action load(Bit#(8) a, Bit#(8) b);
        x <= a;
        y <= b;
    endmethod
    method Nibbles nibbles = ns;
    method TaggedPayload taggedPayload = ts;
endmodule

interface RepackTypes;
    method Action load(Bit#(8) a);
    method Bit#(16) result;
endinterface

// Both nominal interpretations are otherwise absent from module ports/state.
// The only evidence is in evaluated coercions, including cancellations.
(* synthesize *)
module mkRepackTypes(RepackTypes);
    Reg#(Bit#(8)) x <- mkReg(0);
    Bit#(8) bits = x ^ 8'h53;
    Nibbles nv = unpack(bits);
    TaggedPayload tv = unpack(pack(nv));
    method Action load(Bit#(8) a);
        x <= a;
    endmethod
    method Bit#(16) result = {pack(nv), pack(tv)};
endmodule

interface CancellationType;
    method Action load(Bit#(8) a);
    method Bit#(8) result;
endinterface

// pack(unpack(bits)) can cancel, but that very coercion is still evidence
// that the resulting bit expression was used with the Nibbles layout.
(* synthesize *)
module mkCancellationType(CancellationType);
    Reg#(Bit#(8)) x <- mkReg(0);
    Nibbles interpreted = unpack(x ^ 8'h53);
    method Action load(Bit#(8) a);
        x <= a;
    endmethod
    method Bit#(8) result = pack(interpreted);
endmodule

interface ForcedPack;
    method Action load(Bit#(4) hi, Bit#(4) lo);
    method Bit#(8) result;
endinterface

// Constructing a nominal value then packing it requires evaluating its Bits
// method; there is no opposite unpack coercion to cancel.
(* synthesize *)
module mkForcedPack(ForcedPack);
    Reg#(Bit#(4)) hi <- mkReg(0);
    Reg#(Bit#(4)) lo <- mkReg(0);
    method Action load(Bit#(4) h, Bit#(4) l);
        hi <= h;
        lo <= l;
    endmethod
    method Bit#(8) result = pack(Nibbles {upper: hi, lower: lo});
endmodule

interface ForcedUnpack;
    method Action load(Bit#(8) bits);
    method Bit#(4) upper;
    method Bit#(4) lower;
endinterface

// Field selection forces the unpack method. The source interpretation belongs
// to the eight-bit register leaf, not the four-bit field outputs.
(* synthesize *)
module mkForcedUnpack(ForcedUnpack);
    Reg#(Bit#(8)) x <- mkReg(0);
    Nibbles interpreted = unpack(x);
    method Action load(Bit#(8) bits);
        x <= bits;
    endmethod
    method Bit#(4) upper = interpreted.upper;
    method Bit#(4) lower = interpreted.lower;
endmodule

interface LeafInputType;
    method Bit#(4) upper(Bit#(8) bits);
endinterface

// A combinational method argument is an input-port leaf rather than a local
// definition; it still carries the nominal interpretation consumed by unpack.
(* synthesize *)
module mkLeafInputType(LeafInputType);
    method Bit#(4) upper(Bit#(8) bits);
        Nibbles interpreted = unpack(bits);
        return interpreted.upper;
    endmethod
endmodule

interface ConstantType;
    method Bit#(8) result;
endinterface

// The evaluated result is a literal, but the output port is still a wire
// whose source interpretation must survive releasing the evaluator heap.
(* synthesize *)
module mkConstantType(ConstantType);
    method Bit#(8) result = pack(Nibbles {upper: 5, lower: 3});
endmodule

endpackage

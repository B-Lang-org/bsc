package ConditionalTypes;

typedef struct { Bit#(4) upper; Bit#(4) lower; }
    Nibbles deriving (Bits, Eq);
typedef struct { Bit#(3) tag; Bit#(5) payload; }
    TaggedPayload deriving (Bits, Eq);

interface ConditionalTypes;
    method Action load(Bit#(8) a, Bit#(8) b, Bit#(8) c,
                       Bool first, Bool second, Bit#(2) choice);
    method Bit#(8) left;
    method Bit#(8) middle;
    method Bit#(8) right;
    method Bit#(8) selected;
    method Bit#(16) both;
    method Bool predicate;
endinterface

// Each data arm is also an output, so propagation cannot be mistaken for
// annotating only the selected result or a deleted intermediate expression.
(* synthesize *)
module mkConditionalTypes(ConditionalTypes);
    Reg#(Bit#(8)) x <- mkReg(0);
    Reg#(Bit#(8)) y <- mkReg(0);
    Reg#(Bit#(8)) z <- mkReg(0);
    Reg#(Bool) p <- mkReg(False);
    Reg#(Bool) q <- mkReg(False);
    Reg#(Bit#(2)) index <- mkReg(0);
    Bit#(8) a = x ^ 8'h53;
    Bit#(8) b = y ^ 8'ha6;
    Bit#(8) c = z ^ 8'h35;
    Nibbles value = unpack(p ? a : (q ? b : c));
    method Action load(Bit#(8) aa, Bit#(8) bb, Bit#(8) cc,
                       Bool first, Bool second, Bit#(2) choice);
        x <= aa; y <= bb; z <= cc;
        p <= first; q <= second; index <= choice;
    endmethod
    method Bit#(8) left = a;
    method Bit#(8) middle = b;
    method Bit#(8) right = c;
    method Bit#(8) selected = pack(value);
    method Bit#(16) both = {a, b};
    method Bool predicate = p;
endmodule

// Separate selections interpret the shared arm in different nominal layouts.
// CSE must union both sets on that arm, while leaving unrelated arms distinct.
(* synthesize *)
module mkConditionalCseTypes(ConditionalTypes);
    Reg#(Bit#(8)) x <- mkReg(0);
    Reg#(Bit#(8)) y <- mkReg(0);
    Reg#(Bit#(8)) z <- mkReg(0);
    Reg#(Bool) p <- mkReg(False);
    Reg#(Bool) q <- mkReg(False);
    Bit#(8) sharedForNibbles = x ^ 8'h53;
    Bit#(8) sharedForTagged = x ^ 8'h53;
    Bit#(8) b = y ^ 8'ha6;
    Bit#(8) c = z ^ 8'h35;
    Nibbles n = unpack(p ? sharedForNibbles : b);
    TaggedPayload t = unpack(q ? sharedForTagged : c);
    method Action load(Bit#(8) aa, Bit#(8) bb, Bit#(8) cc,
                       Bool first, Bool second, Bit#(2) choice);
        x <= aa; y <= bb; z <= cc;
        p <= first; q <= second;
    endmethod
    method Bit#(8) left = sharedForNibbles;
    method Bit#(8) middle = b;
    method Bit#(8) right = c;
    method Bit#(8) selected = pack(n);
    method Bit#(16) both = {pack(n), pack(t)};
    method Bool predicate = p && q;
endmodule

(* synthesize *)
module mkConditionalCaseTypes(ConditionalTypes);
    Reg#(Bit#(8)) x <- mkReg(0);
    Reg#(Bit#(8)) y <- mkReg(0);
    Reg#(Bit#(8)) z <- mkReg(0);
    Reg#(Bit#(2)) index <- mkReg(0);
    Bit#(8) a = x ^ 8'h53;
    Bit#(8) b = y ^ 8'ha6;
    Bit#(8) c = z ^ 8'h35;
    Bit#(8) selectedBits = case (index)
        0: a;
        1: b;
        default: c;
    endcase;
    Nibbles value = unpack(selectedBits);
    method Action load(Bit#(8) aa, Bit#(8) bb, Bit#(8) cc,
                       Bool first, Bool second, Bit#(2) choice);
        x <= aa; y <= bb; z <= cc; index <= choice;
    endmethod
    method Bit#(8) left = a;
    method Bit#(8) middle = b;
    method Bit#(8) right = c;
    method Bit#(8) selected = pack(value);
    method Bit#(16) both = {a, b};
    method Bool predicate = index == 0;
endmodule

interface ConditionalBoundaries;
    method Action load(Bit#(4) hi, Bit#(4) lo, Bit#(8) inputBits,
                       Bit#(16) wideBits, Bool first, Bool second);
    method Bit#(8) joined;
    method Bit#(8) added;
    method Bit#(8) sliced;
    method Bit#(8) selected;
    method Bit#(4) highInput;
    method Bit#(4) lowInput;
    method Bit#(8) arithmeticInput;
    method Bit#(16) wideInput;
    method Bool predicate;
endinterface

// Conditional alternatives acquire the eight-bit nominal interpretation.
// That interpretation must not cross their arithmetic/concatenation/extract
// boundaries and contaminate separately observable operands.
(* synthesize *)
module mkConditionalBoundaries(ConditionalBoundaries);
    Reg#(Bit#(4)) high <- mkReg(0);
    Reg#(Bit#(4)) low <- mkReg(0);
    Reg#(Bit#(8)) inputValue <- mkReg(0);
    Reg#(Bit#(16)) wide <- mkReg(0);
    Reg#(Bool) p <- mkReg(False);
    Reg#(Bool) q <- mkReg(False);
    Bit#(8) concatValue = {high, low};
    Bit#(8) addValue = inputValue + 8'h13;
    Bit#(8) extractValue = wide[11:4];
    Nibbles value = unpack(p ? concatValue : (q ? addValue : extractValue));
    method Action load(Bit#(4) hi, Bit#(4) lo, Bit#(8) inputBits,
                       Bit#(16) wideBits, Bool first, Bool second);
        high <= hi; low <= lo; inputValue <= inputBits; wide <= wideBits;
        p <= first; q <= second;
    endmethod
    method Bit#(8) joined = concatValue;
    method Bit#(8) added = addValue;
    method Bit#(8) sliced = extractValue;
    method Bit#(8) selected = pack(value);
    method Bit#(4) highInput = high;
    method Bit#(4) lowInput = low;
    method Bit#(8) arithmeticInput = inputValue;
    method Bit#(16) wideInput = wide;
    method Bool predicate = p || q;
endmodule

endpackage

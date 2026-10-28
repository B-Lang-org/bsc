package CandidateSetFlow;
import Vector::*;

typedef struct { Bit#(4) hi; Bit#(4) lo; } Nibbles deriving (Bits, Eq);
typedef struct { Bit#(3) tag; Bit#(5) payload; } Tagged deriving (Bits, Eq);
interface ArrayFlow;
    method Action load(Bit#(8) a, Bit#(8) b, Bit#(8) c, Bit#(2) i);
    method Bit#(8) left;
    method Bit#(8) middle;
    method Bit#(8) right;
    method Bit#(8) selected;
    method Bit#(2) index;
endinterface
(* synthesize *)
module mkArrayFlow(ArrayFlow);
    Reg#(Bit#(8)) x <- mkReg(0);
    Reg#(Bit#(8)) y <- mkReg(0);
    Reg#(Bit#(8)) z <- mkReg(0);
    Reg#(Bit#(2)) ix <- mkReg(0);
    Nibbles a = unpack(x ^ 8'h53);
    Tagged b = unpack(y ^ 8'ha6);
    Bit#(8) c = z ^ 8'h35;
    Vector#(3, Bit#(8)) values = cons(pack(a), cons(pack(b), cons(c, nil)));
    method Action load(Bit#(8) aa, Bit#(8) bb, Bit#(8) cc, Bit#(2) i);
        x <= aa; y <= bb; z <= cc; ix <= i;
    endmethod
    method Bit#(8) left = pack(a);
    method Bit#(8) middle = pack(b);
    method Bit#(8) right = c;
    method Bit#(8) selected = values[ix];
    method Bit#(2) index = ix;
endmodule

typedef enum { F0, F1 } Flag deriving (Bits, Eq);
typedef enum { G0, G1 } OtherFlag deriving (Bits, Eq);
interface FlagSource;
    method Action load(Bit#(1) x);
    method Flag value;
endinterface
interface OtherSource;
    method Action load(Bit#(1) x);
    method OtherFlag value;
endinterface
(* synthesize *)
module mkFlagSource(FlagSource);
    Reg#(Bit#(1)) r <- mkReg(0);
    method Action load(Bit#(1) x); r <= x; endmethod
    method Flag value = unpack(r);
endmodule
(* synthesize *)
module mkOtherSource(OtherSource);
    Reg#(Bit#(1)) r <- mkReg(0);
    method Action load(Bit#(1) x); r <= x; endmethod
    method OtherFlag value = unpack(r);
endmodule
interface OutputFlow;
    method Action load(Bit#(1) a, Bit#(1) b, Bit#(1) c, Bool p, Bool q);
    method Bit#(1) left;
    method Bit#(1) middle;
    method Bit#(1) right;
    method Bit#(1) selected;
    method Bool predicate;
endinterface
// Width-one pack/unpack simplify before evaluator observations, so known
// child output signatures must supply the nominal candidates here.
(* synthesize *)
module mkOutputFlow(OutputFlow);
    FlagSource first <- mkFlagSource;
    OtherSource second <- mkOtherSource;
    Reg#(Bit#(1)) raw <- mkReg(0);
    Reg#(Bool) p <- mkReg(False);
    Reg#(Bool) q <- mkReg(False);
    Bit#(1) a = pack(first.value);
    Bit#(1) b = pack(second.value);
    method Action load(Bit#(1) aa, Bit#(1) bb, Bit#(1) cc, Bool pp, Bool qq);
        first.load(aa); second.load(bb); raw <= cc; p <= pp; q <= qq;
    endmethod
    method Bit#(1) left = a;
    method Bit#(1) middle = b;
    method Bit#(1) right = raw;
    method Bit#(1) selected = p ? a : (q ? b : raw);
    method Bool predicate = p || q;
endmodule
endpackage

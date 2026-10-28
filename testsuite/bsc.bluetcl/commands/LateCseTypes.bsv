package LateCseTypes;

typedef struct { Bit#(1) high; Bit#(1) low; } SimpleInterpretation deriving (Bits, Eq, FShow);
typedef struct { Bit#(1) first; Bit#(1) second; } ExpandedInterpretation deriving (Bits, Eq, FShow);

interface LateCseTypes;
    method Action load(Bool a, Bool b);
    method Bit#(4) result;
    method Bit#(2) simpleResult;
    method Bit#(2) expandedResult;
endinterface

(* synthesize *)
module mkLateCseTypes(LateCseTypes);
    Reg#(Bool) x <- mkReg(False);
    Reg#(Bool) y <- mkReg(False);
    SimpleInterpretation simple = unpack({pack(x), pack(y)});
    ExpandedInterpretation expanded = unpack({pack((x && y) || (x && !y)), pack(y)});
    method Action load(Bool a, Bool b);
        x <= a;
        y <= b;
    endmethod
    method Bit#(4) result = {pack(simple), pack(expanded)};
    method Bit#(2) simpleResult = pack(simple);
    method Bit#(2) expandedResult = pack(expanded);
endmodule

endpackage

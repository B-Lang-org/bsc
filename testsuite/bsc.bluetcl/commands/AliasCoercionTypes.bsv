package AliasCoercionTypes;
import Vector::*;

typedef struct { Bit#(4) high; Bit#(4) low; } Nibbles deriving (Bits);
typedef struct { Bit#(3) tag; Bit#(5) payload; } TaggedPayload deriving (Bits);
interface AliasValue;
    method Bit#(8) value;
endinterface
interface AliasCoercionTypes;
    method Action load(Bit#(8) value);
    interface Vector#(32, AliasValue) aliases;
endinterface

// Many separately written coercions of one expression must join their
// interpretations before expanding the result to the observable aliases.
(* synthesize *)
module mkAliasCoercionTypes(AliasCoercionTypes);
    Reg#(Bit#(8)) x <- mkReg(0);
    Vector#(32, AliasValue) outputs = newVector;
    for (Integer i = 0; i < 32; i = i + 1) begin
        Bit#(8) bits = x + 8'd3;
        Nibbles n = unpack(bits);
        TaggedPayload t = unpack(bits);
        outputs[i] = interface AliasValue;
            method Bit#(8) value = (i % 2 == 0) ? pack(n) : pack(t);
        endinterface;
    end
    method Action load(Bit#(8) value); x <= value; endmethod
    interface aliases = outputs;
endmodule
endpackage

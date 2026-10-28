package ArgumentMuxTypes;

typedef enum { Low, High } Flag deriving (Bits, Eq);

interface FlagSink;
    method Action put(Flag value);
    method Bit#(1) raw;
endinterface

(* synthesize *)
module mkFlagSink(FlagSink);
    Reg#(Flag) stored <- mkReg(Low);
    method Action put(Flag value);
        stored <= value;
    endmethod
    method Bit#(1) raw = pack(stored);
endmodule

interface ArgumentMuxIfc;
    method Action first(Bit#(1) value);
    method Action second(Bit#(1) value);
    method Bit#(1) raw;
endinterface

(* synthesize *)
module mkArgumentMuxTypes(ArgumentMuxIfc);
    FlagSink sink <- mkFlagSink;
    method Action first(Bit#(1) value);
        sink.put(unpack(value));
    endmethod
    method Action second(Bit#(1) value);
        sink.put(unpack(value));
    endmethod
    method Bit#(1) raw = sink.raw;
endmodule

endpackage

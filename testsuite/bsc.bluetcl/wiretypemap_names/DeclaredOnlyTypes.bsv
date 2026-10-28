// Bare Bit ports deliberately require no inferred expression observations.
// The top-level input also collides with the dollar-removed submodule argument.
package DeclaredOnlyTypes;
interface ByteSink;
    method Action put(Bit#(8) payload);
    method Bit#(8) get;
endinterface

(* synthesize *)
module mkDeclaredByteSink(ByteSink);
    Reg#(Bit#(8)) value <- mkReg(0);
    method Action put(Bit#(8) payload);
        value <= payload;
    endmethod
    method Bit#(8) get = value;
endmodule

interface DeclaredOnly;
    (* prefix = "" *)
    method Action send((* port = "sink_put_payload" *) Bit#(8) payload);
    method Bit#(8) result;
endinterface

(* synthesize *)
module mkDeclaredOnlyTypes(DeclaredOnly);
    ByteSink sink <- mkDeclaredByteSink;
    method Action send(Bit#(8) payload);
        sink.put(payload);
    endmethod
    method Bit#(8) result = sink.get;
endmodule
endpackage

package WireTypeMapCases;

import Vector::*;

(* synthesize, no_default_clock, no_default_reset *)
module mkWireTypeMapEmpty(Empty);
endmodule

interface WireTypeMapMany;
    method Bit#(32) total();
endinterface

// Repeated primitive instances exercise deduplication and shared type
// rendering on a larger map. The output keeps every register observable.
(* synthesize *)
module mkWireTypeMapMany(WireTypeMapMany);
    Vector#(128, Reg#(Bit#(32))) values <- replicateM(mkReg(0));

    rule advance;
        for (Integer i = 0; i < 128; i = i + 1)
            values[i] <= values[i] + fromInteger(i + 1);
    endrule

    method Bit#(32) total();
        Bit#(32) result = 0;
        for (Integer i = 0; i < 128; i = i + 1)
            result = result ^ values[i];
        return result;
    endmethod
endmodule

endpackage

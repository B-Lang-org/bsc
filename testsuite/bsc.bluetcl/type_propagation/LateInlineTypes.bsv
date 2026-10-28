package LateInlineTypes;

import RWire::*;

typedef struct { Bit#(4) high; Bit#(4) low; }
    Payload deriving (Bits, Eq);

interface LateTypes;
    method Action put(Bit#(8) x, Bit#(8) y, Bool choose);
    method Payload get;
endinterface

(* synthesize *)
module mkLateCReg(LateTypes);
    Reg#(Bit#(8)) cr[2] <- mkCReg(2, 0);
    method Action put(Bit#(8) x, Bit#(8) y, Bool choose);
        cr[0] <= choose ? x : y;
    endmethod
    method Payload get = unpack(cr[1]);
endmodule

(* synthesize *)
module mkLateRWire(LateTypes);
    RWire#(Bit#(8)) rw <- mkRWire;
    method Action put(Bit#(8) x, Bit#(8) y, Bool choose);
        rw.wset(choose ? x : y);
    endmethod
    method Payload get = unpack(fromMaybe(0, rw.wget));
endmodule

endpackage

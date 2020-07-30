import FIFO::*;
import Vector::*;

interface Ifc;
   method Action m(UInt#(2) idx);
endinterface

(* synthesize *)
module sysMethodCondVecSel(Ifc);
    Vector#(4, FIFO#(Bool)) fs <- replicateM(mkFIFO);

    method Action m(UInt#(2) idx);
       fs[idx].enq(True);
    endmethod
endmodule


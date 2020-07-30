import FIFO::*;
import Vector::*;

interface Ifc;
   method Bit#(8) get();
endinterface

// We use aggressive conditions here to create a case in the impl cond,
// so that we're testing both arrays and case stmts
//
(* synthesize *)
(* options = "-aggressive-conditions" *)
module sysDynArrSelWithImplCond (Ifc);
   Vector#(4, FIFO#(Bit#(8))) fs <- replicateM(mkFIFO);
   Reg#(UInt#(2)) idx <- mkReg(0);

   method get() = fs[idx].first;
endmodule


package WrapperRedirectSeed;

import Vector::*;

// Export a package containing lifted Ord, Eq, Literal, and Arith dictionaries
// for Bit#(8), so the importing package's matching dictionaries are removed.
function Bit#(8) seed(Bit#(8) x);
   return (x == 0 || x < 4) ? x + 1 : x - 1;
endfunction

interface BoolRegs;
   interface Vector#(2, Reg#(Bool)) regs;
endinterface

// These wrapper dictionaries are also available for cross-package deduplication.
(* synthesize *)
module mkSeedBoolRegs(BoolRegs);
   Vector#(2, Reg#(Bool)) rs <- replicateM(mkReg(False));
   interface regs = rs;
endmodule

endpackage

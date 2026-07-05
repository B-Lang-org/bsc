package ShadowLockUseBsv;

// Cross-package, BSV syntax: instance compiles, unqualified and
// qualified uses resolve to the wrapper (17).
import ShadowLock::*;

typedef struct { Bit#(1) f; } X deriving (Eq);

instance C5#(X);
   function Bit#(8) m5(X x) = 9;
endinstance

(* synthesize *)
module mkShadowLockUseBsv(IfcSL);
   method out = m5(X { f: 0 }) + ShadowLock::m5(MkV) - 17;
endmodule

endpackage

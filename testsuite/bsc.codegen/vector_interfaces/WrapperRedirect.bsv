package WrapperRedirect;

import Vector::*;
import WrapperRedirectSeed::*;

// Initial fixup drops these imported-equal arithmetic dictionaries.  Their
// names must remain reserved: reusing them for the generated wrapper's
// differently typed dictionaries would trigger stale cached redirects.
function Bit#(8) localAdd(Bit#(8) x);
   return (x == 0 || x < 4) ? x + seed(2) : x - 1;
endfunction

(* synthesize *)
module mkWrapperRedirect(BoolRegs);
   Vector#(2, Reg#(Bool)) rs <- replicateM(mkReg(False));
   interface regs = rs;
endmodule

// If the first wrapper's dictionaries are dropped in favor of imported ones,
// this second wrapper must still reserve every name allocated by the first.
(* synthesize *)
module mkWrapperRedirectSecond(BoolRegs);
   Vector#(2, Reg#(Bool)) rs <- replicateM(mkReg(False));
   interface regs = rs;
endmodule

endpackage

interface Ifc;
   method Bool m1();
   method Bool m2();
endinterface

import "BVI"
module mkSub (Ifc);
   method OUT m1();
   method OUT m2();
   schedule (m1, m2) CF (m1, m2);
endmodule

// Declare a no-inline function, which should be treated by the solver
// as an unevaluated function, whose arguments can at least be analyzed
// (and a function applied to equivalent arguments is equivalent)
(* noinline *)
function Bool id(Bool b);
   return b;
endfunction

(* synthesize *)
module sysSharedPortsInArg();
   Ifc i <- mkSub;

   Reg#(Bit#(16)) rg <- mkReg(0);

   rule do1 (id( i.m1 ));
      // make the rules conflict via a shared register
      rg <= rg - 1;
   endrule

   rule do2 (id( ! i.m2 ));
      // make the rules conflict via a shared register
      rg <= rg + 1;
   endrule
endmodule

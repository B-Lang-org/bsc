// This example, when compiled with -aggressive-conditions,
// lifts the value part of an actionvalue into the predicate,
// which is bad because it breaks atomicity (if, say, the rule
// then chooses not to fire).

// If the actionvalue method has arguments, and if any are used
// to compute the return value, then path analysis detects a
// cycle, because the arguments are supplied in the body of the
// rule and the return value depends on the arguments, but the
// return value is used in the predicate -- so the predicate depends
// on the body, which is not allowed.

// This example is without arguments.

import FIFO::*;

interface SubIFC;
   method ActionValue#(Bool) f();
endinterface

(* synthesize *)
module mkSub (SubIFC);
   Reg#(Bool) b <- mkReg(False);
   method ActionValue#(Bool) f;
      b <= !b;
      return b;
   endmethod
endmodule

(* synthesize *)
module mkTop (Empty);
   SubIFC sub <- mkSub;
   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;
   rule bad_rule;
      Bool p <- sub.f;
      if (p)
	 f1.enq(True);
      else
	 f2.enq(True);
   endrule
endmodule

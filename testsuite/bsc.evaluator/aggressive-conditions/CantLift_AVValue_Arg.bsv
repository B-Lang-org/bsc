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

// This example is with an argument that determines the return value.

import FIFO::*;

interface SubIFC;
   method ActionValue#(Bool) f(Bool v);
endinterface

(* synthesize *)
module mkSub2 (SubIFC);
   Reg#(Bool) b <- mkReg(False);
   method ActionValue#(Bool) f(Bool v);
      b <= !v;
      // if this is just "return b", there is no cycle detected
      return b && v;
   endmethod
endmodule

(* synthesize *)
module mkTop2 (Empty);
   SubIFC sub <- mkSub2;
   Reg#(Bool) r <- mkReg(False);
   FIFO#(Bool) f1 <- mkFIFO;
   FIFO#(Bool) f2 <- mkFIFO;
   rule bad_rule;
      Bool p <- sub.f(r);
      if (p)
	 f1.enq(True);
      else
	 f2.enq(True);
   endrule
endmodule

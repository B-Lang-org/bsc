// Rules with private state whose predicates all read bits of one
// module parameter: the rule predicates share support without the
// rules sharing any state instance.  Locks the schedule (and the
// absence of spurious conflicts) for the case where predicate-level
// disjointness testing is restricted to consulted pairs.
import Vector::*;

(* synthesize *)
module mkGuardedRules#(parameter Bit#(64) cfg)(Empty);
  Vector#(64, Reg#(UInt#(16))) rs <- replicateM(mkReg(0));
  for (Integer i = 0; i < 64; i = i + 1)
    rule incr (cfg[i] == 1);
      rs[i] <= rs[i] + 1;
    endrule
endmodule

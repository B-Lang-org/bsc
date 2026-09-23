// Many rules all writing one shared register: every rule pair truly
// conflicts, so this locks the schedule computed for a dense conflict
// clique (blocker lists, urgency choices, and the arbitrary-choice
// warnings) against behavioral drift in the scheduler's pair
// enumeration.
(* synthesize *)
module mkDenseRules(Empty);
  Reg#(UInt#(32)) shared_r <- mkReg(0);
  Reg#(UInt#(32)) cnt <- mkReg(0);
  for (Integer i = 0; i < 64; i = i + 1)
    rule bump (cnt < fromInteger(i + 1));
      shared_r <= shared_r + fromInteger(i + 1);
    endrule
endmodule

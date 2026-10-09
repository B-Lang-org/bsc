package PartialOutputCommit;

// A7, positive half through the PARTIAL commit path: the tuple
// instance's fundep output (TAdd#(m, p)) commits while m and p are
// still metavariables and its context (the recursive Sz subgoals) is
// not yet discharged; the subgoals then resolve and the arithmetic
// proves.

typeclass Sz#(type a, type n) dependencies (a determines n);
  function Bit#(n) enc(a x);
endtypeclass

instance Sz#(Bool, 1);
  function enc(x) = x ? 1 : 0;
endinstance

instance Sz#(Tuple2#(a, b), TAdd#(m, p)) provisos (Sz#(a, m), Sz#(b, p), Add#(m, p, TAdd#(m, p)));
  function enc(x) = {enc(tpl_1(x)), enc(tpl_2(x))};
endinstance

(* synthesize *)
module mkPartialOutputCommit();
  rule r;
    let e = enc(tuple2(True, False));
    Bit#(8) y = zeroExtend(e);
    $display(y);
  endrule
endmodule
endpackage

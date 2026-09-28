package IncoherentNumBatch;

// An incoherent-class match never adopts on unproven numeric debt:
// its selected instance's numeric proviso gets a local verdict.  The
// proviso is chosen so only the solver can prove it: the use is
// polymorphic (n rigid), so Add#(n, n, m) is not ground, and the
// only given is Mul#(n, 2, m) -- a cross-class entailment no
// commuted given or direct instance can discharge.  If the local
// batch did not settle it, the match would look partial and
// selection would fall to the catch-all, whose result type Bit#(n)
// cannot satisfy the signature's Bit#(m).

typeclass incoherent Pick#(type a, type b) dependencies (a determines b);
  function b pick(a x);
endtypeclass

instance Pick#(Bit#(n), Bit#(m)) provisos (Add#(n, n, m));
  function pick(x) = {x, x};
endinstance

instance Pick#(a, a);
  function pick(x) = x;
endinstance

function Bit#(m) doublePick(Bit#(n) x) provisos (Mul#(n, 2, m));
  return pick(x);
endfunction

(* synthesize *)
module mkIncoherentNumBatch();
  rule r;
    Bit#(4) v = 9;
    Bit#(8) doubled = doublePick(v);
    $display(doubled);
  endrule
endmodule
endpackage

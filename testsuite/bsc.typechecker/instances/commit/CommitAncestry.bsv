package CommitAncestry;

// A coherent unique match commits even though its numeric proviso is
// unsatisfiable; the error reports the instance's obligation with the
// use site that introduced it, rather than backing the match out and
// reporting an unreduced context.

typeclass Sized#(type a);
  function Bit#(8) measure(a x);
endtypeclass

// n + n = 13 has no solution
instance Sized#(Bit#(n)) provisos (Add#(n, n, 13));
  function measure(x) = 0;
endinstance

(* synthesize *)
module mkCommitAncestry();
  rule r;
    Bit#(4) v = 5;
    $display(measure(v));
  endrule
endmodule
endpackage

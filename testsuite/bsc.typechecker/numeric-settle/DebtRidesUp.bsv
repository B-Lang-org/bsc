package DebtRidesUp;

// A local function with no numeric givens cannot prove its numeric
// obligation locally; the debt rides up (unqueried) to the enclosing
// definition, whose proviso proves it.  The obligation is chosen so
// that only the solver can prove it: from Mul#(a, 2, b) prove
// Add#(a, a, b) -- a cross-class entailment (2a = b |- a + a = b)
// that no direct instance can synthesize (the output position is
// pinned to b) and no commuted given can supply.

function Bit#(b) outer(Bit#(a) x) provisos (Mul#(a, 2, b));
  function Bit#(b) inner(Bit#(a) p);
    return {p, p};
  endfunction
  return inner(x);
endfunction

(* synthesize *)
module mkDebtRidesUp();
  rule r;
    Bit#(3) x = 5;
    $display(outer(x));
  endrule
endmodule
endpackage

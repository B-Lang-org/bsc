// A divide-by-zero that the design correctly guards against, but which
// Bluesim evaluates anyway.  The rule is unconditional and the guard is
// in the rule body, so the generated C++ computes a / b unconditionally
// and only gates the write.  (A guard on the rule itself would instead
// stop the rule from firing at all, and the division would never run.)
//
// Both backends must agree that r keeps its initial value.  Before the
// divide-by-zero fix this was undefined behavior in Bluesim: at -O0 the
// division was emitted ahead of the guard and raised SIGFPE, while at
// higher optimization levels gcc sank it inside the guard and the test
// passed by accident.

module sysDivideByZeroGuarded();

Reg#(UInt#(16)) a <- mkReg(1203);
Reg#(UInt#(16)) b <- mkReg(0);
Reg#(UInt#(16)) r <- mkReg(7);

Reg#(Bool) done <- mkReg(False);

rule test (!done);
  if (b != 0) r <= a / b;
  done <= True;
endrule

rule quit (done);
  $display(r);
  $finish(0);
endrule

endmodule

// Create a module with a rule that conflicts with a value
// method and is more urgent than it.
interface Bug;
  method Bool get();
endinterface

(* synthesize *)
module mkBug(Bug);

  Reg#(Bool)   r  <- mkReg(False);
  RWire#(Bool) w  <- mkRWire();
  RWire#(Bool) w2 <- mkRWire();

  (* descending_urgency="put,r2" *)
  rule put;
    r <= True;
    w.wset(True);
  endrule

  rule r2 (w.wget() matches tagged Valid .x);
    w2.wset(!x);
  endrule

  // the put rule conflicts with this method and is
  // more urgent.  since the put rule is unconditional,
  // this method can never be ready.
  method Bool get() if (isValid(w2.wget()));
    if (w.wget() matches tagged Valid .x)
      return x;
    else
      return r;
  endmethod

endmodule

(* synthesize *)
module sysRulePreemptsValueMethod();

  Bug b <- mkBug();

  // This rule should never fire because b.get() should never
  // be ready.
  rule test;
    $display("%b", b.get());
    $finish(0);
  endrule

endmodule
interface Bug;

  method ActionValue#(Bool) update(Bool x);

endinterface

(* synthesize, always_enabled *)
module mkBug(Bug);

  Reg#(Bool) r1 <- mkReg(True);

  method ActionValue#(Bool) update(Bool x);
    r1 <= x;
    return r1;    
  endmethod

endmodule

(* synthesize *)
module sysMethodNeverEnabled();

  Reg#(Bool) r1 <- mkReg(False);
  Reg#(Bool) r2 <- mkReg(False);
  Bug bug <- mkBug();

  (* descending_urgency="swap,do_update" *)
  rule swap;
    r1 <= r2;
    r2 <= r1;
  endrule

  rule do_update;
    let x <- bug.update(r1);
    r2 <= x;
  endrule

endmodule
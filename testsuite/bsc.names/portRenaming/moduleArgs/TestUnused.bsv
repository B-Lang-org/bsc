import Clocks::*;

(* synthesize, default_gate_unused *)
module sysTestUnused();

  Reg#(Bool) r1 <- mkReg(False);

  rule print;
    $display(r1);
    r1 <= !r1;
  endrule

endmodule
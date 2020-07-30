(* synthesize *)
(* no_default_reset *)
module sysNoDefaultReset_Port#(Reset rst, Bool p)();
  Reg#(Bool) rg <- mkReg(True, reset_by rst);

  // This should not generate a multiple-reset warning
  // because the port should be associated with no_reset
  rule r;
    rg <= p;
  endrule
endmodule

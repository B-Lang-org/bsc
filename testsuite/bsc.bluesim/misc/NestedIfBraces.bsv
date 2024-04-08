

ActionValue #(Bit #(32)) cur_cycle = actionvalue
                                        Bit #(32) t <- $stime;
                                        if (genVerilog)
                                          t = t + 5;
                                        return t / 10;
                                     endactionvalue;

(* synthesize *)
module sysNestedIfBraces ();

  Reg #(Bit #(4)) cfg_verbosity <- mkReg (1);

  Reg #(Bool) rg_state <- mkReg (False);

  rule rl_display (! rg_state);
    if (cfg_verbosity != 0)
      $display ("%0d: display", cur_cycle);
    rg_state <= True;
  endrule

  rule rl_finish (rg_state);
    $finish (0);
  endrule

endmodule


(* synthesize *)
module sysMutuallyExclusiveBug1327();

  PulseWire step <- mkPulseWire;

  Reg#(Bool) mode <- mkReg(True);

  Reg#(Bit#(21)) r <- mkReg(0);

  Reg#(Bit#(19)) count <- mkReg(0);
  
  rule doit;
    count <= count + 1;
    if(count == 1) $finish(0);
  endrule

  (* mutually_exclusive="step_True, set_r_in_step_false" *)
  rule step_True(mode);
    step.send;
    r <= 17;
    $display("step_true: %0d", count);
    mode <= False;
  endrule

  rule step_False(!mode);
    step.send;
  endrule

  // should also have && !mode
  rule set_r_in_step_false(step);
    r <= r + 1;
    $display("set_r_in_step_false: %0d", count);
  endrule

endmodule

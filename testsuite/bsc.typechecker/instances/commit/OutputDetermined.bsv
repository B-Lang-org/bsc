package OutputDetermined;

// A7 (positive half): a sole matching instance's fundep output
// commits while the output position is still a metavariable --
// sole-instance output determination is the workhorse of numeric
// resolution and must not be blocked by commitment discipline.

(* synthesize *)
module mkOutputDetermined();
  rule r;
    let x = pack(True);          // Bits#(Bool, sz) commits sz := 1
    Bit#(8) y = zeroExtend(x);   // Add#(1, k, 8) then proves
    $display(y);
  endrule
endmodule
endpackage

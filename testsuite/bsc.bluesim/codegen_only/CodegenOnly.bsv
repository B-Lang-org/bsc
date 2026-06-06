// Minimal one-module design for testing -sim-codegen-only
module mkCodegenOnly();
  rule done;
    $display("done");
    $finish(0);
  endrule
endmodule

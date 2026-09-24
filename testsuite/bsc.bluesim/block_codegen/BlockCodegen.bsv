// Minimal one-module design for testing the -c codegen mode
module mkBlockCodegen();
  rule done;
    $display("done");
    $finish(0);
  endrule
endmodule

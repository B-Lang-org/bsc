(* synthesize *)
module sysLogBaseNegative();
    Real x = logb(-2,4);

    rule r;
      $display("logb(-2,4) = " + realToString(x));
    endrule
endmodule
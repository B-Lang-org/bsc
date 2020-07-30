(* synthesize *)
module sysLogBaseZero();
    Real x = logb(0,12);

    rule r;
      $display("logb(0,12) = " + realToString(x));
    endrule
endmodule
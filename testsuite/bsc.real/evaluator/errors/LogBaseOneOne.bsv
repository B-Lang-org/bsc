(* synthesize *)
module sysLogBaseOneOne();
    Real x = logb(1,1);

    rule r;
      $display("logb(1,1) = " + realToString(x));
    endrule
endmodule
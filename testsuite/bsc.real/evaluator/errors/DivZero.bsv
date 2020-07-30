(* synthesize *)
module sysDivZero();
    Real x = 12 / 0;

    rule r;
      $display("12 / 0 = " + realToString(x));
    endrule
endmodule
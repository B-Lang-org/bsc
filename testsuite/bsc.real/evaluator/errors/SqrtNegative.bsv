import Real::*;

(* synthesize *)
module sysSqrtNegative();
    real y = sqrt(-4.0);

    rule r;
      $display("sqrt(-4.0) = " + realToString(y));
    endrule
endmodule
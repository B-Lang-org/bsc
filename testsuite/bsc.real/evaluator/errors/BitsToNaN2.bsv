(* synthesize *)
module sysBitsToNaN2();

    // NaN (if e = 2047 and f !=0)
    // Test with sign == 1
    Bit#(1) sign2 = 1;
    Bit#(52) mantissa2 = 17;
    Bit#(11) exp2 = 2047;
    Real r2 = $bitstoreal({sign2, exp2, mantissa2});

    function m(s) = $display(message(s,s));

    rule r;
      m("r2 = " + realToString(r2));
    endrule
endmodule


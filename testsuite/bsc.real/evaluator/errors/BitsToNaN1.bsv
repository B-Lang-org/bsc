(* synthesize *)
module sysBitsToNaN1();

    // NaN (if e = 2047 and f !=0)
    // Test with sign == 0
    Bit#(1) sign1 = 0;
    Bit#(52) mantissa1 = 17;
    Bit#(11) exp1 = 2047;
    Real r1 = $bitstoreal({sign1, exp1, mantissa1});

    function m(s) = $display(message(s,s));

    rule r;
      m("r1 = " + realToString(r1));
    endrule
endmodule


(* synthesize *)
module sysBits();

    // $realtobits

    Real w = 2;
    Bit#(64) wb = $realtobits(w);
    Bit#(1) wb_sign = wb[63:63];
    Bit#(52) wb_mantissa = wb[51:0];
    Bit#(11) wb_exp = wb[62:52];

    Bit#(64) nwb = $realtobits(-w);
    Bit#(1) nwb_sign = nwb[63:63];
    Bit#(52) nwb_mantissa = nwb[51:0];
    Bit#(11) nwb_exp = nwb[62:52];

    Bit#(64) w2b = $realtobits(w * (2 ** 10));
    Bit#(1) w2b_sign = w2b[63:63];
    Bit#(52) w2b_mantissa = w2b[51:0];
    Bit#(11) w2b_exp = w2b[62:52];

    Bit#(64) w3b = $realtobits(w + 0.5);
    Bit#(1) w3b_sign = w3b[63:63];
    Bit#(52) w3b_mantissa = w3b[51:0];
    Bit#(11) w3b_exp = w3b[62:52];

    // $bitstoreal

    // normalized (positive)
    Bit#(1) sign1 = 0;
    Bit#(52) mantissa1 = 0;
    Bit#(11) exp1 = 1024;
    Real r1 = $bitstoreal({sign1, exp1, mantissa1});

    // normalized (negative)
    Bit#(1) sign2 = 1;
    Bit#(52) mantissa2 = 1 << 51;
    Bit#(11) exp2 = 1024;
    Real r2 = $bitstoreal({sign2, exp2, mantissa2});

    // Inf (if e = 2047 and f == 0)
    Bit#(1) sign3 = 0;
    Bit#(52) mantissa3 = 0;
    Bit#(11) exp3 = 2047;
    Real r3 = $bitstoreal({sign3, exp3, mantissa3});

    // -INF
    Bit#(1) sign4 = 1;
    Real r4 = $bitstoreal({sign4, exp3, mantissa3});

    // Zero (if e == 0 and f == 0)
    Bit#(1) sign5 = 0;
    Bit#(52) mantissa5 = 0;
    Bit#(11) exp5 = 0;
    Real r5 = $bitstoreal({sign5, exp5, mantissa5});

    // -Zero
    Bit#(1) sign6 = 1;
    Real r6 = $bitstoreal({sign6, exp5, mantissa5});

    // denormalized (positive)
    Bit#(1) sign7 = 0;
    Bit#(52) mantissa7 = 3 << 49;
    Bit#(11) exp7 = 0;
    Real r7 = $bitstoreal({sign7, exp7, mantissa7});

    // denormalized (negative)
    Bit#(1) sign8 = 1;
    Bit#(52) mantissa8 = 3 << 48;
    Bit#(11) exp8 = 0;
    Real r8 = $bitstoreal({sign8, exp8, mantissa8});

    function m(s) = $display(message(s,s));

    rule r;
      m("w = 2.0 = " + realToString(w));
      m("w bits = (" +
         bitToString(wb_sign) + ", " +
         bitToString(wb_mantissa) + ", " +
         bitToString(wb_exp) + ")");
      m("-w bits = (" +
         bitToString(nwb_sign) + ", " +
         bitToString(nwb_mantissa) + ", " +
         bitToString(nwb_exp) + ")");
      m("w2 bits = (" +
         bitToString(w2b_sign) + ", " +
         bitToString(w2b_mantissa) + ", " +
         bitToString(w2b_exp) + ")");
      m("w3 bits = (" +
         bitToString(w3b_sign) + ", " +
         bitToString(w3b_mantissa) + ", " +
         bitToString(w3b_exp) + ")");
      m("w3 mantissa should be " + integerToString(2**50));

      m("r1 = " + realToString(r1));
      m("r2 = " + realToString(r2));
      m("r3 = " + realToString(r3));
      m("r4 = " + realToString(r4));
      m("r5 = " + realToString(r5));
      m("r6 = " + realToString(r6));
      m("r7 = " + realToString(r7));
      m("r8 = " + realToString(r8));
    endrule
endmodule


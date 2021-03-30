(* synthesize *)
module sysOpPrecedence();
  Reg #(Bool) done <- mkReg(False);

  rule runTest (!done);
    done <= True;

    // To reduce the number of tests, we assume that precedence is transitive,
    // so we only have to test each level vs the level next to it

    // Test ** vs * (and / and % ?)
    Real r1 = (-1 * 2) ** 4;
    $display("r1 = (-1 * 2) ** 4 = %s", realToString(r1));
    Real r2 = -1 * (2 ** 4);
    $display("r2 = -1 * (2 ** 4) = %s", realToString(r2));
    Real r3 = -1 * 2 ** 4;
    $display("r3 = -1 * 2 ** 4 = %s (should equal r2)", realToString(r3));

    $display("");

    // Test unary !, ~, &, |, ^ vs *
    // (because ** isn't defined on types which have bit operators defined)
    // !! Can't even test this ("& 3 * 4") because types prevent confusing
    // !! the output of "&" with anything other than Bit#(1).

    // Test + - vs << >>
    Bit#(8) b1_2 = (1 << 3) + 2;
    $display("b1 = (1 << 3) + 2 = %b", b1_2);
    Bit#(8) b2_2 = 1 << (3 + 2);
    $display("b2 = 1 << (3 + 2) = %b", b2_2);
    Bit#(8) b3_2 = 1 << 3 + 2;
    $display("b3 = 1 << 3 + 2 = %b (should equal b2)", b3_2);

    // Test << >> vs < <= > >=
    // XXX

    // XXX Test more precedence levels

    // XXX Could test same level ops vs each other, and test associativity

  endrule

  rule endTest (done);
    $finish(0);
  endrule

endmodule


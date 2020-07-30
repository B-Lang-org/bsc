module sysMinimalRuleWarnings(Empty);
    Reg#(Bit#(8)) r();
    mkReg#(0) the_r(r);

    rule theRuleOne (r > 10);
      action
        r <= r + 23;
      endaction
    endrule

    rule theRuleTwo (r > 7);
      action
        r <= r + 2;
      endaction
    endrule

    rule theRuleThree (r > 5);
      action
        r <= 2*r - 13;
      endaction
    endrule

    rule theRuleFour (r > 1);
      action
        r <= r +1;
      endaction
    endrule


endmodule

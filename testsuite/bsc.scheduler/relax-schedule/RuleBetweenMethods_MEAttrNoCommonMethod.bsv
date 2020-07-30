(* synthesize *)
module sysRuleBetweenMethods_MEAttrNoCommonMethod ();
    SubIfc s <- mkRuleBetweenMethods_MEAttrNoCommonMethod_Sub;
    Reg#(Bool) p1 <- mkReg(True);
    Reg#(Bool) p2 <- mkReg(False);

    Reg#(int) rg1 <- mkRegU;
    Reg#(int) rg2 <- mkRegU;
    Reg#(int) rg3 <- mkRegU;

    (* mutually_exclusive = "top_rule_r1, top_rule_r2" *)
    rule top_rule_r1 (p1);
      s.m1();
      rg1 <= 17;
    endrule

    rule top_rule_r2 (p2);
      s.m2();
      rg3 <= rg2;
    endrule

    // insert a rule between, to enforce an opposite order from the use of "s"
    rule top_rule_middle;
      rg2 <= rg1;
    endrule

endmodule

interface SubIfc;
    method Action m1();
    method Action m2();
endinterface

// Execution order: m1, sub_rule, m2
(* synthesize *)
module mkRuleBetweenMethods_MEAttrNoCommonMethod_Sub (SubIfc);
    Reg#(int) rg1 <- mkRegU;
    Reg#(int) rg2 <- mkRegU;
    Reg#(int) rg3 <- mkRegU;

    rule sub_rule;
      rg2 <= rg1;
    endrule

    method Action m1();
      rg3 <= rg2;
    endmethod

    method Action m2();
      rg1 <= 17;
    endmethod
endmodule

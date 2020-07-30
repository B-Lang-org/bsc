(* synthesize *)
module sysRuleBetweenMethods_Loop_TwoME();

  // for mutual exclusion
  Reg#(Bool) p1 <- mkRegU;
  Reg#(Bool) p2 <- mkRegU;

  // for ordering
  Reg#(Bool) rg1 <- mkRegU;
  Reg#(Bool) rg2 <- mkRegU;
  // to create an action
  Reg#(Bool) rg3 <- mkRegU;
  Reg#(Bool) rg4 <- mkRegU;

  SBRSub sub1 <- mkRuleBetweenMethods_Loop_TwoME_Sub;
  SBRSub sub2 <- mkRuleBetweenMethods_Loop_TwoME_Sub;

  // ME with r2 (but implied SB because of submethod calls)
  rule r1(p1);
    rg2 <= !rg2;
    sub1.a;
  endrule

  // SB with r3
  rule r2(!p1);
    rg3 <= rg1;
    sub1.b;
  endrule

  // ME with r4 (but implied SB because of submethod calls)
  rule r3(p2);
    rg1 <= !rg1;
    sub2.a;
  endrule

  rule r4(!p2);
    rg4 <= rg2;
    sub2.b;
  endrule

endmodule

interface SBRSub;
  method Action a;
  method Action b;
endinterface

(* synthesize *)
module mkRuleBetweenMethods_Loop_TwoME_Sub(SBRSub);

  Reg#(Bool) one <- mkRegU;
  Reg#(Bool) two <- mkRegU;
  Reg#(Bool) three <- mkRegU;

  rule middle;
     two <= one;
     three <= two;
  endrule

  method Action a;
     three <= !three;
  endmethod

  method Action b;
     one <= True;
  endmethod

endmodule


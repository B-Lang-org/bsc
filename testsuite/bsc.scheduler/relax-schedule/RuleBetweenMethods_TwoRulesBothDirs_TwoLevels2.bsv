
(* synthesize *)
module sysRuleBetweenMethods_TwoRulesBothDirs_TwoLevels2();
   Reg#(Bool) p <- mkReg(False);

   SubIfc s1 <- mkSub_Wrapper;
   SubIfc s2 <- mkSub_Wrapper;
 
   rule top_rule_A (p);
      s1.m1(s2.m2);
   endrule

   rule top_rule_B (!p);
      s2.m1(s1.m2);
   endrule
endmodule

interface SubIfc;
   method Action m1(int x);
   method int m2();
endinterface

(* synthesize *)
module mkSub_Wrapper(SubIfc);
   SubIfc s <- mkSub_Core;

   Reg#(Bool) p <- mkRegU;
   Reg#(int) count <- mkReg(0);

   // here, this rule still has to come before m2,
   // and it is disjoint with m1, but it has to come
   // after m1 because of the use of methods on "s".
   // So ... BSC should realize that m1/m2 have a rule between them
   // (two, in fact)
   rule sub_rule (p);
      count <= count + s.m2;
   endrule

   method Action m1(x) if (!p);
      s.m1(x);
   endmethod
   
   method int m2();
      return (count);
   endmethod
endmodule

(* synthesize *)
module mkSub_Core(SubIfc);
   Reg#(int) en <- mkRegU;
   Reg#(int) count <- mkRegU;

   rule sub_rule (en < 100);
      count <= count + 1;
   endrule
      
   method Action m1(int x);
      en <= x;
   endmethod
   
   method int m2();
      return (count);
   endmethod

endmodule


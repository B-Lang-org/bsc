
(* synthesize *)
module sysRuleBetweenMethods_TwoRulesBothDirsDisjoint();
   Reg#(Bool) p <- mkReg(False);

   SubIfc s1 <- mkRuleBetweenMethods_TwoRulesBothDirsDisjoint_Sub;
   SubIfc s2 <- mkRuleBetweenMethods_TwoRulesBothDirsDisjoint_Sub;
 
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
module mkRuleBetweenMethods_TwoRulesBothDirsDisjoint_Sub(SubIfc);
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


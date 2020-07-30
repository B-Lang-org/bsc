
(* synthesize *)
module sysRuleBetweenMethods_TwoRulesBothDirs_TwoLevels();
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
   return s;
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


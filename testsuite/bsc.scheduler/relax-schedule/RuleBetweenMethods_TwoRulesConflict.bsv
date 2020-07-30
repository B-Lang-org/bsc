// Test for Bug 1401

(* synthesize *)
module sysRuleBetweenMethods_TwoRulesConflict ();

   SubIfc sub <- mkRuleBetweenMethods_TwoRulesConflict_Sub;

   // conditions for top_rule_1 and top_rule_3, so they only sometimes fire
   Reg#(Bool) p1 <- mkRegU;
   Reg#(Bool) p3 <- mkRegU;

   // register which makes top_rule_1 and top_rule_3 conflict
   Reg#(Bool) c <- mkRegU;
   
   // register which makes top_rule_3 execute after top_rule_2
   Reg#(Bool) rg23 <- mkRegU;
   // register which makes top_rule_2 execute after top_rule_1
   Reg#(Bool) rg12 <- mkRegU;
   
   rule top_rule_3 (p3);
      // call the method
      $display(sub.method1);
      // execute after top_rule_2
      rg23 <= True;
      // conflict with top_rule_3
      c <= !c;
   endrule

   rule top_rule_2;
      // execute after top_rule_1, before top_rule_3
      rg12 <= rg23;
   endrule

   // because it conflicts with top_rule_3, the conflicts between
   // sub.method1 and sub.method2 are ignored
   (* descending_urgency = "top_rule_1, top_rule_3" *)
   rule top_rule_1 (!p1);
      // call the method
      sub.method2;
      // execute before top_rule_1
      $display(rg12);
      // conflict with top_rule_3
      c <= !c;
   endrule

endmodule

interface SubIfc;
   method Bool   method1();
   method Action method2();
endinterface

(* synthesize *)
module mkRuleBetweenMethods_TwoRulesConflict_Sub ( SubIfc );

   Reg#(Bool) rg1 <- mkRegU;
   Reg#(Bool) rg2 <- mkRegU;

   // Exec order:  method1, sub_rule, method2

   rule sub_rule;
        rg1 <= rg2;
   endrule            

   method Action method2();
      rg2 <= True;
   endmethod

   method Bool method1 = rg1;

endmodule

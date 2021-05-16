
interface SubIfc;
   method Action am1(int x);
   method Action am2(int x);
   method Action am3(int x);
   method int vm1();
   method int vm2();
   method int vm3();
endinterface

(* synthesize *)
module sysRuleBetweenMethods_TwoLevels_MultipleMethods(SubIfc);
   SubIfc s <- mkRuleBetweenMethods_TwoLevels_MultipleMethods_Core;
   return s;
endmodule

(* synthesize *)
module mkRuleBetweenMethods_TwoLevels_MultipleMethods_Core(SubIfc);
   Reg#(int) en1 <- mkRegU;
   Reg#(int) en2 <- mkRegU;
   Reg#(int) en3 <- mkRegU;
   Reg#(int) en4 <- mkRegU;

   Reg#(int) val1 <- mkRegU;
   Reg#(int) val2 <- mkRegU;

   Reg#(int) count <- mkRegU;

   rule sub_rule_btwn_am1_am2 (en2 < 100);
      val1 <= val1 + 1;
   endrule

   rule sub_rule_btwn_am2_am3 (en3 < 100);
      val2 <= val2 + 1;
   endrule

   rule sub_rule_btwn_am1_am3 (en3 < 100);
      val1 <= val1 + 1;
   endrule

   rule sub_rule_btwn_vms_am1 (en1 < 100);
      count <= count + 1;
   endrule

   rule sub_rule_btwn_vms_am2 (en2 < 100);
      count <= count + 1;
   endrule

   rule sub_rule_btwn_vms_am3 (en3 < 100);
      count <= count + 1;
   endrule

   method Action am1(int x);
      en1 <= val1 & x;
   endmethod

   method Action am2(int x);
      en2 <= val2 & x;
   endmethod

   method Action am3(int x);
      en3 <= x;
   endmethod

   method int vm1();
      return (count + 1);
   endmethod

   method int vm2();
      return (count + 2);
   endmethod

   method int vm3();
      return (count + 3);
   endmethod

endmodule


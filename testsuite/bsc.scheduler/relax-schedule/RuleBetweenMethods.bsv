// Test for bug 1362

(* synthesize *)
module sysRuleBetweenMethods();
   Reg#(Bool) p <- mkReg(False);
   SubIfc s <- mkRuleBetweenMethods_Sub;
 
   rule top_rule;
      if (p)
	 s.m1;
      else
	 $display("%d", s.m2);
   endrule
endmodule

interface SubIfc;
   method Action m1();
   method int m2();
endinterface

(* synthesize *)
module mkRuleBetweenMethods_Sub(SubIfc);
   Reg#(Bool) en <- mkReg(False);
   Reg#(int) count <- mkReg(0);

   rule sub_rule (en);
      count <= count + 1;
   endrule
      
   method Action m1();
      en <= !en;
   endmethod
   
   method int m2();
      return (count);
   endmethod

endmodule


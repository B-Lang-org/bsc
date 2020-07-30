
(* synthesize *)
module sysRuleBetweenMethods_TwoLevels2();
   Reg#(Bool) p <- mkReg(False);
   SubIfc s <- mkSub_Wrapper;
 
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

   method Action m1() if (!p);
      s.m1;
   endmethod
   
   method int m2();
      return (count);
   endmethod
endmodule

(* synthesize *)
module mkSub_Core(SubIfc);
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


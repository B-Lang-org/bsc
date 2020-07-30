import Design::* ;
(* synthesize *)
module top(Empty);
   Design_in_IFC t1();
   mkDesign_in  foo(t1);
endmodule

(* synthesize *)
module top2(Empty);
   Design_IFC t1();
   mkDesign foo(t1);
   rule every (True);
      t1.calc(1,1,1,1);
   endrule
endmodule

(* synthesize *)
module top3(Empty);
   Joint_IFC t1();
   foo ifoo(t1);
endmodule

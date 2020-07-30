package AttrDemo;
module mkAttrDemoSub (Empty);
   (* doc = "breadcrumb" *)
   Reg#(int) bar <- mkRegU;
endmodule

(* synthesize *)
module mkAttrDemo (Empty);
   for (Integer i=0; i < 8; i=i+1)
      Empty baz <- mkAttrDemoSub;
endmodule
endpackage

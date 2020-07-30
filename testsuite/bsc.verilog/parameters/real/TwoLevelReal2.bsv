(* synthesize *)
module bsvDisplayReal#(parameter real r)(Empty ifc);
   
   rule test;
      $display("real number: %3.1f", r);
      $finish(0);
   endrule

endmodule


(* synthesize *)
module mkRealPassThrough2#(parameter Real r)();
   bsvDisplayReal(r);
endmodule

(* synthesize *)
module sysTwoLevelReal2();
   mkRealPassThrough2(243.179);
endmodule

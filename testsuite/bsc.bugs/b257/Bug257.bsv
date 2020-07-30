interface Test;
   method Action foo(Bit#(32) a);
endinterface

(* synthesize *)
module mkTest(Test);

   Reg#(Bit#(32)) foo_a <- mkReg(0);
   
   method Action foo(a);
      foo_a <= a;
   endmethod
   
endmodule

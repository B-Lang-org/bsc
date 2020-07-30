interface IFC;
   method Action m1();
   method Action m2();
endinterface

(* synthesize *)
module mkAmbiguousEarlinessMethodMethod (IFC);
  Reg#(int) r <- mkReg(0);

  method Action m1();
    r <= 24;
  endmethod

  method Action m2();
    r <= 42;
  endmethod
endmodule

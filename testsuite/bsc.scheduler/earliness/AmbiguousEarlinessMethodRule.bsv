// Test that an earliness warning is reported between a method and rule
// (at least when -relax-method-earliness is on)

interface IFC;
   method Action m();
endinterface

(* synthesize *)
module mkAmbiguousEarlinessMethodRule (IFC);
  Reg#(int) r <- mkReg(0);

  rule ambiguity_two;
    r <= 24;
  endrule

  method Action m();
    r <= 42;
  endmethod
endmodule

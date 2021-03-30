interface IFC;
   method Bool m(Bool a1, Bool a2);
endinterface

(* synthesize *)
module sysNonSynthesizedModule ();
   Reg#(Bool) r1 <- mkRegU;
   Reg#(Bool) r2 <- mkRegU;
   IFC s <- mkNonSynthesizedModule_Sub;
   rule r;
      r1 <= s.m(r1,r2);
   endrule
endmodule

module mkNonSynthesizedModule_Sub (IFC);
   method Bool m(Bool a2, Bool a1);
      return (a1 && !a2);
   endmethod
endmodule


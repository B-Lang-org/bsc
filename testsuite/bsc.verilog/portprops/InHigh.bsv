interface SubIFC;
   method Action start();
   method Bool result();
endinterface

interface TopIFC;
   method Action start();
   method Bool result();
endinterface

(* synthesize, always_enabled, always_ready *)
module mkSub (SubIFC);
   Reg#(Bool) r <- mkRegU;
   method Action start();
      r <= True;
   endmethod
   method Bool result;
      return r;
   endmethod
endmodule

// mkTop's methods are not always_enabled so there should be an error.
// will bsc give the start enable an inhigh property?
(* synthesize *)
module mkTop (TopIFC);
   SubIFC s <- mkSub;
   method Action start();
      s.start;
   endmethod
   method Bool result;
      return s.result;
   endmethod
endmodule

// if the inhigh property is propagated to mkTop's start method
// and the const property propagated to the RDY of the result method,
// then an error should not result here,
// because the rule will always fire
(* synthesize *)
module mkTest1 (Empty);
   TopIFC t <- mkTop;
   Reg#(Bool) b <- mkReg(False);
   rule try (t.result);
      t.start();
   endrule
endmodule

// an error should be asserted here because the rule will not always fire
(* synthesize *)
module mkTest2 (Empty);
   TopIFC t <- mkTop;
   Reg#(Bool) b <- mkReg(False);
   rule try (b && t.result);
      t.start();
   endrule
endmodule

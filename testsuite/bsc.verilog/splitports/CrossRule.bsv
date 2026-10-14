interface Sub;
   method Action put(Tuple2#(Bit#(4), Bit#(8)) x);
endinterface

(* synthesize *)
module mkCrossRuleSub(Sub);
   Reg#(Bit#(4)) r1 <- mkReg(0);
   Reg#(Bit#(8)) r2 <- mkReg(0);
   method Action put(Tuple2#(Bit#(4), Bit#(8)) x);
      r1 <= tpl_1(x);
      r2 <= tpl_2(x);
   endmethod
endmodule

(* synthesize *)
module sysCrossRule(Empty);
   Sub s <- mkCrossRuleSub;
   Reg#(Bool) c <- mkReg(False);
   Reg#(Bit#(4)) a <- mkReg(0);
   Reg#(Bit#(8)) b <- mkReg(0);
   rule r1 (c);
      s.put(tuple2(a, 8'h11));
   endrule
   rule r2 (!c);
      s.put(tuple2(a, b));
   endrule
endmodule

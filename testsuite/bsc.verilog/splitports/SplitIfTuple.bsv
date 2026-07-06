// Minimal reproducer for the AVerilog vDefMpd tuple ICE:
// two conditional calls to the same tuple-argument Action method in one
// rule are merged by ILift into one call with an if-of-tuple argument,
// which nothing downstream can lower.
interface Sub;
   method Action put(Tuple2#(Bit#(4), Bit#(8)) x);
endinterface

(* synthesize *)
module mkSplitIfTupleSub(Sub);
   Reg#(Bit#(4)) r1 <- mkReg(0);
   Reg#(Bit#(8)) r2 <- mkReg(0);
   method Action put(Tuple2#(Bit#(4), Bit#(8)) x);
      r1 <= tpl_1(x);
      r2 <= tpl_2(x);
   endmethod
endmodule

(* synthesize *)
module sysSplitIfTuple(Empty);
   Sub s <- mkSplitIfTupleSub;
   Reg#(Bool) c <- mkReg(False);
   Reg#(Bit#(4)) a <- mkReg(0);
   Reg#(Bit#(8)) b <- mkReg(0);
   rule go;
      if (c)
         s.put(tuple2(a, 8'h11));
      else
         s.put(tuple2(a, b));
   endrule
endmodule

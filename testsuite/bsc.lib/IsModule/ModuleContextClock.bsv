import ModuleContext::*;

typedef ModuleContext#(Integer) Module2;

module [Module2] mkTest#(Clock c)();
  
   Integer i <- getContext;
   putContext (i + 1);

   Reg#(Bit#(32)) r <- mkRegU(clocked_by c);
   
   rule test;
      r <= r + 1;
   endrule
   
endmodule

(* synthesize *)
module [Module] mkTestWrapper2#(Clock c)();
   
   let _m <- runWithContext(0, mkTest(c));
   
   messageM(integerToString(tpl_1(_m)));

endmodule

   

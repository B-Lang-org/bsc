import ModuleCollect::*;

typedef ModuleCollect#(Integer) Module2;

module [Module2] test(Empty);
 Reg#(Bit#(32)) r <- mkReg(0); 
endmodule: test

(* synthesize *)
module sysUseMod2Arrow(Empty);
  IWithCollection#(Integer, Empty) e <- exposeCollection(test);
endmodule: sysUseMod2Arrow


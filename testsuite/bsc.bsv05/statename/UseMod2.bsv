package UseMod2;

import ModuleCollect::*;

typedef ModuleCollect#(Integer) Module2;

module [Module2] test(Empty);
 Reg#(Bit#(32)) r(); 
 mkReg#(0) the_r(r);
endmodule: test

(* synthesize *)
module sysUseMod2(Empty);
  IWithCollection#(Integer, Empty) e();
  exposeCollection#(test) the_e(e);
endmodule: sysUseMod2

endpackage: UseMod2

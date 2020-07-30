package ParamOrder ;

interface Ptest_Ifc;
   method Action go() ;
endinterface

import "BVI" Param =
module  mkParam#(Integer a, Integer b, Integer c)( Ptest_Ifc) ;
   
   default_clock (CLK) ;
   default_reset ()  ;
   
   // Parameter must be in same order as Verilog
   parameter C = c;
   parameter A = a;
   parameter B = b;
   
   method go()  enable(GO) ready(RDY_GO);
      
endmodule


(* synthesize *)
module sysParamOrder() ;
   Ptest_Ifc  dut <- mkParam(1, 10 , 1000);
   
   rule fire ;
      dut.go ;
   endrule
endmodule

endpackage

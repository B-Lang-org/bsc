

import TesterLib::*;
import FPLibrary::*;
import FPAdd::*;


// sys* modules are top level test drivers


(* synthesize *)
module sysTesterA(Empty) ;

   QBinOp#(IEEE754_32) dut_ifc() ;
   mkFPAdd dut_a(dut_ifc) ;

   Empty i0() ;
   mkTester #(dut_ifc, "testa.dat") dut_a_tester(i0) ;
endmodule


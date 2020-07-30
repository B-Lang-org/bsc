import TesterLib::*;
import FPLibrary::*;
import FPAddAssertBug::*;

// sys* modules are top level test drivers
(* synthesize *)
module sysTesterBug(Empty) ;

   QBinOp#(IEEE754_32) dut_ifc() ;
   mkFPAddAssertBug dut_a(dut_ifc) ;

   Empty i0() ;
   mkTester#(dut_ifc, "testa.dat") dut_a_tester(i0) ;
endmodule

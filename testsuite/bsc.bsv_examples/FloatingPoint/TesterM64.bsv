import TesterLib::*;
import FPLibrary::*;
import FPMult::*;

// sys* modules are top level test drivers

(* synthesize *)
module sysTesterM64(Empty) ;
   QBinOp#(IEEE754_64) dut_ifc() ;
   mkFPMult64 dut_m(dut_ifc) ;

   Empty i0() ;
   mkTester #(dut_ifc, "testm64.dat") dut_m64_tester(i0) ;
endmodule

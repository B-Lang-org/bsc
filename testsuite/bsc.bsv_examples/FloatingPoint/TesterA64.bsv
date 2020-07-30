import TesterLib::*;
import FPLibrary::*;
import FPAdd::*;

// sys* modules are top level test drivers

(* synthesize *)
module sysTesterA64(Empty) ;

   QBinOp#(IEEE754_64) dut_ifc() ;
   mkFPAdd64 dut_a64(dut_ifc) ;

   Empty i0() ;
   mkTester #(dut_ifc, "testa64.dat") dut_a64_tester(i0) ;
endmodule


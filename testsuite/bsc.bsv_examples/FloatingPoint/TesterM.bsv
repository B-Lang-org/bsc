import TesterLib::*;
import FPLibrary::*;
import FPMult::*;

// sys* modules are top level test drivers



(* synthesize *)
module sysTesterM(Empty) ;
   QBinOp#(IEEE754_32) dut_ifc() ;
   mkFPMult dut_m(dut_ifc) ;

   Empty i0() ;
   mkTester #(dut_ifc, "testm.dat") dut_m_tester(i0) ;
endmodule


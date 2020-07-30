import TesterLib::*;
import FPLibrary::*;
import FPMac::*;

// sys* modules are top level test drivers
(* synthesize *)
module sysTesterMac64(Empty) ;
   QTerOp#(IEEE754_64) dut_ifc() ;
   mkFPMac64 imac(dut_ifc) ;
   
   Empty i0() ;
   mkTester3 #(dut_ifc, "testmac64.dat") dut(i0) ;
endmodule








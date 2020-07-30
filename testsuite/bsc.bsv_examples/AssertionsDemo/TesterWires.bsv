import TesterLib::*;
import FPLibrary::*;
import FPAddAssertWires::*;
import AssertionWires::*;

// sys* modules are top level test drivers
(* synthesize *)
module sysTesterWires(Empty);

   AssertIfc#(QBinOp#(IEEE754_32), 1) dut_ifc() ;
   mkFPAddAssertWires dut_a(dut_ifc) ;

   Empty i0() ;
   mkTester#(dropAssertionWires(dut_ifc), "testa.dat") dut_a_tester(i0) ;

   AssertionWires#(1) wires = getAssertionWires(dut_ifc);

   rule check;
     wires.clear;
     if(wires.wires != 0)
       $display("Time: %0t hiddenBit: FAIL", $time);
   endrule

endmodule



// import FPLibrary::*;
import FPAdd::*;
// import FPMac::*;
import RegFile::* ;
import FIFO::*;

typedef Tuple3#( IEEE754_32, IEEE754_32, IEEE754_32) TestData_t;
typedef Tuple4#( IEEE754_32, IEEE754_32, IEEE754_32, IEEE754_32) TestData3_t;


(* synthesize *)
module mkTesterA(Empty) ;

   QBinOp#(IEEE754_32) dut_ifc() ;
   mkFPAdd dut(dut_ifc) ;

   Empty i0() ;
   mkTester #(dut_ifc, "testa.dat") dut(i0) ;
endmodule

// (* synthesize *)
// module mkTesterM(Empty) ;
//    QBinOp#(IEEE754_32) dut_ifc() ;
//    mkFPMult dut(dut_ifc) ;

//    Empty i0() ;
//    mkTester #(dut_ifc, "testm.dat") dut(i0) ;
// endmodule

// Generate tester for Binary operations
module mkTester #(QBinOp#(IEEE754_32) dut_ifc,
                  String testfile)
   ( Empty ) ;

   // an array holding the test data
   RegFile#(Bit#(7), TestData_t )  test_ifc();
   mkRegFileFullLoad#(testfile) iarray(test_ifc) ;
   
   // An index to the array
   Reg#(Bit#(7) )  counter() ;
   mkReg#(0) icounter(counter) ;

   FIFO#(IEEE754_32) result_q();
   mkSizedFIFO#(4) iresultq(result_q) ;

   // queue the data from the array to the adder.
   rule test (True) ;
      action
         TestData_t test ;
         counter <= counter + 1 ;
         test = test_ifc.sub(counter) ;
         dut_ifc.start(tpl_1(test), tpl_2(test) );
         result_q.enq( tpl_3(test) ) ;
      endaction
   endrule

   rule check (True) ;
      action
         dut_ifc.deq() ;
         result_q.deq() ;
         IEEE754_32 result   = dut_ifc.result() ;
         IEEE754_32 expected = result_q.first() ;
         if ( result == expected )
            begin
               $display( "Result is equal -- %h", result );
            end
         else
            begin
               $display( "Result is different -- %h %h    %b  %b",
                        result, expected, result, expected );
            end
      endaction
   endrule

   rule vcd (counter == 0 ) ;
      $dumpvars();
   endrule
   
   
   rule fine (counter == ( 7'h7f )) ;
      action
         $finish(1);
      endaction
   endrule
   
endmodule

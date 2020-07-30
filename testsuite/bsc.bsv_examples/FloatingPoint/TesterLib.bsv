package TesterLib;

import FIFO::*;
import RegFile::*;
import RegFile::*;

// Interface for a module which has a binary operation, e.g. add, mult
interface QBinOp #(parameter type a);
   method Action start( a inA, a inB );
   method a result();
   method Action deq () ;
endinterface

// Interface for a module which has a ternary operation, e.g. MAC 
interface QTerOp #(parameter type a);
   method Action start3( a inA, a inB, a inC );
   method a result();
   method Action deq () ;
endinterface


// parameterized module taking a function as an argument
module mkFPBinOp #(function t fun ( t a, t b) ) (QBinOp #(t) ) 
                      provisos( Bits#(t,st) ) ;

   FIFO#(t) outfifo() ;
   mkFIFO i_outfifo(outfifo) ;

   FIFO#(Tuple2#(t,t)) infifo() ;
   mkFIFO i_infifo(infifo) ;

   rule crunch ;
      action
         let {arg1, arg2} = infifo.first ;
         infifo.deq ;
         outfifo.enq( fun( arg1, arg2 )) ;
      endaction
   endrule


   method start( inA, inB );
      action
         infifo.enq( tuple2( inA, inB ) ) ;
      endaction
   endmethod

   method result() ;
      return outfifo.first ;
   endmethod

   method deq() ; action
      outfifo.deq ;
   endaction endmethod

endmodule


module mkFPTerOp
   #( function t fun ( t c, t a, t b) )
           (QTerOp #(t) )
         provisos( Bits#(t,st), Eq#(t) );

   FIFO#(t) outfifo() ;
   mkFIFO i_outfifo(outfifo) ;

   FIFO#(Tuple3#(t,t,t)) infifo() ;
   mkFIFO i_infifo(infifo) ;

   rule crunch ;
      action
         let {arg1, arg2, arg3 } = infifo.first ;
         infifo.deq ;
         outfifo.enq( fun( arg1, arg2, arg3 ) ) ;
      endaction
   endrule


   method start3( inA, inB, inC );
      action
         infifo.enq( tuple3( inA, inB, inC ) ) ;
      endaction
   endmethod

   method result() ;
      return outfifo.first ;
   endmethod

   method deq() ; action
      outfifo.deq ;
   endaction endmethod

endmodule


// Generic tester for Binary operations
module mkTester #(QBinOp#(t) dut_ifc,
                  String testfile) 
   ( Empty )
   provisos( Bits#(t,st), Eq#(t), Literal#(t) )  ;

   // an array holding the test data
   RegFile#(Bit#(7), Tuple3#(t,t,t) )  test_ifc();
   mkRegFileFullLoad#(testfile) iarray(test_ifc) ;
   
   // An index to the array
   Reg#(Bit#(7) )  counter() ;
   mkReg#(0) icounter(counter) ;

   // An index to the array
   Reg#(Bit#(7) )  error_count() ;
   mkReg#(0) ecounter(error_count) ;

   FIFO#(t) result_q();
   mkSizedFIFO#(4) iresultq(result_q) ;

   // queue the data from the array to the adder.
   rule test ;
      action
         counter <= counter + 1 ;
         let {arg1, arg2, result} = test_ifc.sub(counter) ;
         // Termination condition is when all data are equal and non zero
         if (!(( arg1 == arg2 ) && (arg2 == result ) && (result != 0)))
            begin
               dut_ifc.start( arg1, arg2 );
               result_q.enq( result ) ;
            end
      endaction
   endrule

   rule check ;
      action
         dut_ifc.deq() ;
         result_q.deq() ;
         t result   = dut_ifc.result() ;
         t expected = result_q.first() ;
         if ( result == expected )
            begin
               $display( "Result is equal -- %h", result );
            end
         else
            begin
               error_count <= error_count + 1 ;
               $display( "Result is different -- %h %h    %b  %b",
                        result, expected, result, expected );
            end
      endaction
   endrule

   rule vcd (counter == 0 ) ;
      $dumpvars();
   endrule


   rule finish_sim (counter == ( 7'h7f )) ;
      action
         $finish(0);
      endaction
   endrule
   
endmodule

// Generate tester for Ternary operations
module mkTester3 #(QTerOp#(t) dut_ifc,
                  String testfile)
   ( Empty ) 
   provisos( Bits#(t,st), Eq#(t), Literal#(t), Bitwise#(t) );


   // an array holding the test data
   RegFile#(Bit#(7), Tuple4#(t,t,t,t) )  test_ifc();
   mkRegFileFullLoad#(testfile) iarray(test_ifc) ;
   
   // An index to the array
   Reg#(Bit#(7) )  counter() ;
   mkReg#(0) icounter(counter) ;

   FIFO#(t) result_q();
   mkSizedFIFO#(4) iresultq(result_q) ;

   // queue the data from the array to the adder.
   rule test ;
      action
         counter <= counter + 1 ;
         let {arg1, arg2, arg3, result} = test_ifc.sub(counter) ;
         // Termination condition is when all data are equal and non zero
         if (!(( arg1 == arg2 ) && (arg2 == arg3) && (arg3 == result ) && (result != 0)))
            begin
               dut_ifc.start3( arg1, arg2, arg3 ) ;
               result_q.enq( result ) ;
            end
      endaction
   endrule

   rule check ;
      action
         dut_ifc.deq() ;
         result_q.deq() ;
         let result = dut_ifc.result() ;
         let expected = result_q.first() ;

         // For ternary operations, rounding may be different,
         // especially with 64 bit machines.  Hence we drop the
         // comparison on the lsb
         let resultc   = ~ 'b01 & dut_ifc.result() ;
         let expectedc = ~ 'b01 & result_q.first() ;

         if ( resultc == expectedc )
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
   
   
   rule finish_sim (counter == ( 7'h7f )) ;
      action
         $finish(0);
      endaction
   endrule
      
endmodule


endpackage

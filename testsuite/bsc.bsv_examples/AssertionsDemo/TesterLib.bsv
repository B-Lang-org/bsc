package TesterLib;

import FIFO::*;
import RegFile::*;

// Interface for a module which has a binary operation, e.g. add, mult
interface QBinOp #(parameter type a);
   method Action start( a inA, a inB );
   method Maybe#(a) result();
   method Action deq () ;
endinterface

// parameterized module taking a function as an argument
module mkFPBinOp #(function t fun ( t a, t b) ) (QBinOp #(t) ) 
                      provisos( Bits#(t,st) ) ;

   FIFO#(t) outfifo() ;
   mkFIFO i_outfifo(outfifo) ;

   FIFO#(Tuple2#(t,t)) infifo() ;
   mkFIFO i_infifo(infifo) ;

   Reg#(Bool) flip();
   mkReg#(False) i_flip(flip);

   RWire#(t) forward();
   mkRWire i_forward(forward);

   rule do_flip;
     flip <= !flip;
   endrule

   rule crunch(flip);
      action
         let {arg1, arg2} = infifo.first ;
         infifo.deq ;
         outfifo.enq( fun( arg1, arg2 )) ;
      endaction
   endrule

   rule forward_result;
     forward.wset(outfifo.first);
   endrule

   method start( inA, inB );
      action
         infifo.enq( tuple2( inA, inB ) ) ;
      endaction
   endmethod

   method result() ;
      return forward.wget;
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

   rule check(dut_ifc.result() matches tagged Valid .result);
      action
         dut_ifc.deq() ;
         result_q.deq() ;
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


endpackage

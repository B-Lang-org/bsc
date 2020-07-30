package MaxTree ;

import Vector::* ;
import Push::* ;
import GetPut::* ;
import FIFO::*;


// The type of data which is compared.  This can be any type provided there
// is a compare function, and the it is an instance of Bits
typedef Bit#(5) BaseData;


// The input data a listN of size n of BaseData
typedef Vector#(n, BaseData )
  StartData #(type n) ;

// The output data, the max BaseData, and its index.
typedef Tuple2#( Bit#(TLog#(n)), BaseData )
  ReturnData #(type n) ;

// A simple of an iterface defining just wires
typedef Tuple2#(  StartData#(n), ReturnData#(n) )
  Port_Wires #(type n) ;


//interface Ifc_simple used for pure combinational blocks -- no actions
interface Ifc_Simple #(type n) ;
  method ReturnData#(n) results ( StartData#(n) indata ) ;
endinterface

//interface Ifc_simple used for registered --
// load method is an action
interface Ifc_MaxTree_Load #(type n) ;
  method Action load ( StartData#(n) indata );
  method ReturnData#(n) results () ;
endinterface


// interface with methods to push (loadit), sample (get) and take (dequeue) action
//  from the pipeline
interface Ifc_MaxTree_Queues #(type n);
  method Action          pushit ( StartData#(n) indata );
  method Action          takeit () ;
  method ReturnData#(n)  get () ;
endinterface


// Using and interface composed of Put and Get interfaces from the Library
// This can also be replace with the ClientServer interface
interface   Ifc_MaxQ #(type n ) ;
   interface Put#( StartData#(n) ) inputSide;
   interface Get#( ReturnData#(n) ) outputSide ;
endinterface



//

// function taking list of size n and return list of size n/2
// moreover, the the output data in modified to build up the index of the
// selected term.
// The list selection is accomplished through the comparison function which is the first
// argument in this function.  This is an example of higher-order function use in
//  hardware design.
function Vector#(nn, Tuple2#(Bit#(aa), bb))
  cullList (
           function Bool comparer( bb x1, bb x2 ), // function as an argument
           Vector#(n, Tuple2#(Bit#(a), bb)) indata
              )
    // the provision define sized for index part of the data and list
    provisos ( Add#(a, 1, aa ),
               Div#(n, 2, nn )
               );

      // nested function which does the comparison and updates the index
      function Tuple2#(Bit#(aa), bb)
        cullPair (
                   Tuple2#(Bit#(a), bb) in1,
                   Tuple2#(Bit#(a), bb) in2 );
      begin
         Bit#(aa) nextIndex;
         bb  outdata ;

         let {index1,data1} = in1 ;
         let {index2,data2} = in2 ;
         if ( comparer( data1, data2) ) begin
            outdata = data1;
            nextIndex = {1'b0, index1 } ;
         end
         else begin
            outdata = data2 ;
            nextIndex = {1'b1, index2} ;
         end
         return tuple2( nextIndex, outdata ) ;
      end
      endfunction // cullPair

      // Main function body
      begin
         // Uses the mapPair library function
         return (mapPairs ( cullPair, error("maxpair"), indata )) ;
      end
endfunction // cullList

// Function convert any data type bb into list for processing
// through cullList
// No hardware is generated for this, just a type change.
// Note use of Bit#(0)
function Vector#(n, Tuple2#(Bit#(0), bb))
      wrapStartData ( Vector#(n, bb) datain ) ;
      begin
         Vector#(n, Bit#(0) ) index0 ;
         index0 = replicate( 0 ) ;
         return (zip (index0 , datain )) ;
      end
endfunction


// A specific comparison function for BaseData
// used as an argument in cullList
function Bool comp1( BaseData in1, BaseData in2 );
begin
   return in1 > in2 ;
end
endfunction


//
(* synthesize *)
// Create module with takes a list of 8 BaseData, and return the index
// of the largest BaseData and the BaseData.
// note that sizes can be changed by modifying interface argument and
// number of composed functions.
module mkMaxTree8_p0 ( Ifc_Simple#(8) ) ;

   // define maxpair a specific version of cullList which take uses comp1
   // as a comparison function, and then consumes BaseData
   let maxpair = cullList( comp1 ) ;

   method results ( indata ) ;
   begin
      // Nested function calls -- outputs to inputs
      results = head(
                      maxpair(
                      maxpair(
                      maxpair(
                                wrapStartData( indata )
                                )))) ;

      // the wrapStartData function places the data into the Vector type
      // 3 calls to cullList (through maxpair are done, since log 8 = 3.
      // and the head extracts the data out of the listN
   end
   endmethod
endmodule


// Same variation with a 16 element input, and one extra function stage
(* synthesize *)
module mkMaxTree16_p0 ( Ifc_Simple#(16) ) ;

   let maxpair = cullList( comp1 ) ;
   method results ( indata ) ;
   begin
      // Nested function calls.
      results = head(
                      maxpair(
                      maxpair(
                      maxpair(
                      maxpair(
                                wrapStartData( indata )
                                ))))) ;
   end
   endmethod
endmodule


//
(*
 synthesize
*)
// Making module with size 8 input and 1 register delay at input
// interface now has action method for load.
module mkMaxTest8_p1_in ( Ifc_MaxTree_Load#(8) ) ;

   Reg#(StartData#(8)) state0() ;
   // The unpack function used to convert from literal 0 to proper type
   // in this case StartData#(8)
   mkReg#(unpack(0)) i_state0(state0) ;

   let maxpair = cullList( comp1 ) ;


   method load( indata ) ;          // load the in data to  register state0
   action
     state0 <=  indata  ;
   endaction
   endmethod

   method results ( ) ;        // get the results which instantiates the function
   begin
      // Nested function calls.
      results = head(
                      maxpair(
                      maxpair(
                      maxpair(
                                wrapStartData( state0  ) )))) ;
   end
   endmethod


endmodule

//
(*
 synthesize
*)
// Making module with size 8 input and 1 register delay at output
// interface now has action method for load.
module mkMaxTree_p1_out ( Ifc_MaxTree_Load#(8) ) ;

   Reg#(ReturnData#(8)) state0() ;
   // The unpack function used to convert from literal 0 to proper type
   // in this case a ReturnData#(8)
   mkReg#(unpack(0)) i_state0(state0) ;

   let maxpair = cullList( comp1 ) ;
   method load( indata ) ;          // load the state register with the result of
                                // the max tree
   action
     state0 <= head(
                     maxpair(
                     maxpair(
                     maxpair(
                                wrapStartData( indata  ) )))) ;
   endaction
   endmethod

   method results ( ) ;        // output just gets the register value
   begin
      // Nested function calls.
      results = state0 ;
   end
   endmethod


endmodule

//
// Using the Push Library and Interface
// The Push package provides several methods to combine functions
// into pipeline using wires, registers, or FIFOs to combine the stages
// This design is the functionally equivalent to mkMaxTree_p1_out
(* synthesize *)
module mkMaxTree8_push ( Ifc_MaxTree_Load#(8) );

   Reg#(ReturnData#(8)) reg_ifc() ;
   mkReg#(unpack(0)) i_reg(reg_ifc) ;
   // Use the library function regToPush to convert the Reg interface to a Push
   Push#(ReturnData#(8)) pu_ifc = regToPush( reg_ifc ) ;

   let maxpair = cullList( comp1 ) ;

   // Using a Push interface
   Push#( StartData#(8) ) processor ;

   processor <- pipe( passed(wrapStartData),
                pipe( passed(maxpair),
                pipe( passed(maxpair),
                pipe( passed(maxpair),
                      passed(head, pu_ifc)
                       ))));

   // The passed function wraps its function argument into the Push Interface
   // while the pipe function connects the interfaces together without hardware

   method results ;
     return reg_ifc ;
   endmethod

   method load ( indata ) ;
   action
     processor.push( indata ) ;
   endaction
   endmethod
endmodule


//
// Using the Push Library and Interface
//(* synthesize *)
// Modify from the above, by using an output fifo and adding a pipeline stage in the
// tree processing
module mkMaxTree8_p2_fifo ( Ifc_MaxTree_Queues#(8) );

   FIFO#(ReturnData#(8)) fifo_out() ;
   mkFIFO  i_fifoout(fifo_out) ;
   Push#(ReturnData#(8)) pu_fifo_out = fifoToPush( fifo_out ) ;

   let maxpair = cullList( comp1 ) ;

   // Using a Push interface
   Push#( StartData#(8) ) processor ;
   processor <- pipe( passed(wrapStartData),
                pipe( passed(maxpair),
                      // the registered buffer is prior to function application
                pipe( q1buffered(maxpair),
                pipe( passed(maxpair),
                      passed(head, pu_fifo_out)
                       ))));

   method pushit ( indata ) ;   action
     processor.push( indata );
   endaction endmethod

   method get ;
       return fifo_out.first ;
   endmethod

   method takeit ; action
       fifo_out.deq ;
    endaction  endmethod

endmodule

//(* synthesize *)
// Another variation, tree selects from 128
// 2 pipeline stages added in culling tree
// Changing only data type causes type error, so the hardware must be changed as
// well.
module mkMaxTree128_p3 ( Ifc_MaxTree_Queues#(128) );

   FIFO#(ReturnData#(128)) fifo_out() ;
   mkFIFO  i_fifoout(fifo_out) ;
   Push#(ReturnData#(128)) pu_fifo_out = fifoToPush( fifo_out ) ;

   let maxpair = cullList( comp1 ) ;

   // Using a Push interface
   Push#( StartData#(128) ) processor ;

   processor <- pipe( passed(wrapStartData),
                pipe( passed(maxpair),
                      // the registered buffer is prior to function application
                pipe( passed(maxpair),
                pipe( q1buffered(maxpair),
                pipe( passed(maxpair),
                pipe( passed(maxpair),
                pipe( q1buffered(maxpair),
                pipe( passed(maxpair),
                      passed(head, pu_fifo_out)
                       ))))))));

   method pushit ( indata ) ;   action
     processor.push( indata );
   endaction endmethod

   method get ;
       return fifo_out.first ;
   endmethod

   method takeit ; action
       fifo_out.deq ;
    endaction  endmethod

endmodule



//
// Using the Push Library and Interface
(* synthesize *)
// Modify from the above, by using an input fifo, and an output fifo
module mkMaxTree8_2q ( Ifc_MaxTree_Queues#(8) );

   FIFO#(StartData#(8)) fifo_in() ;
   mkFIFO  i_fifoin(fifo_in) ;

   FIFO#(ReturnData#(8)) fifo_out() ;
   mkFIFO  i_fifoout(fifo_out) ;
   // Use the library function regToPush to convert the FIFO interface to a Push
   Push#(ReturnData#(8)) pu_fifo_out = fifoToPush( fifo_out ) ;

   let maxpair = cullList( comp1 ) ;

   // Using a Push interface
   Push#( StartData#(8) ) processor ;

   processor <- pipe( passed(wrapStartData),
                pipe( passed(maxpair),
                pipe( passed(maxpair),
                pipe( passed(maxpair),
                      passed(head, pu_fifo_out)
                       ))));

   // Rules -- to move data from input to output
   rule movepipe ;
     processor.push( fifo_in.first );
     fifo_in.deq() ;
   endrule

   method pushit ( indata ) ;   action
     fifo_in.enq( indata ) ;
   endaction endmethod

   method takeit ; action
       fifo_out.deq ;
   endaction  endmethod

   method get ;
      return fifo_out.first ;
   endmethod
endmodule


//
(* synthesize *)
// Modified from the above, by using different interface
module mkMaxTree8_getput ( Ifc_MaxQ#(8) );

   FIFO#(StartData#(8)) fifo_in() ;
   mkFIFO  i_fifoin(fifo_in) ;

   FIFO#(ReturnData#(8)) fifo_out() ;
   mkFIFO  i_fifoout(fifo_out) ;
   // Use the library function regToPush to convert the Reg interface to a Push
   Push#(ReturnData#(8)) pu_fifo_out = fifoToPush( fifo_out ) ;

   let maxpair = cullList( comp1 ) ;

   // Using a Push interface
   Push#( StartData#(8) ) processor ;

   processor <- pipe( passed(wrapStartData),
                pipe( passed(maxpair),
                pipe( passed(maxpair),
                pipe( passed(maxpair),
                      passed(head, pu_fifo_out)
                       ))));

   // Rules -- to move data from input to output
   rule movepipe ;
     processor.push( fifo_in.first );
     fifo_in.deq() ;
   endrule

   // This module provides an interface of interfaces, so there definition
   // add another level of indirection.
   interface Put inputSide ;
      method put ( indata ) ;
         action
            fifo_in.enq( indata ) ;
         endaction
      endmethod
   endinterface

   interface Get outputSide ;
      method get ;
         actionvalue
            fifo_out.deq ;
            return fifo_out.first ;
         endactionvalue
      endmethod
   endinterface


endmodule


endpackage

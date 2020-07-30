package TestPush;
// A package which shows an example use of the Push library.

// Import some additional libraries showing how Push can be used with these.
import FIFO::*;
import Push::*;
import LFSR::*;


// Generic Data type
typedef Bit#(4) Data_t ;

// An example function it just adds 2
function Data_t add2 ( Data_t inp );
      begin
         return 2 + inp ;
      end
endfunction //


// An external interface 
interface Pusher;
  // An action method to push data into the module
  method Action go(Data_t in2);

  // a simple way to sample out of the module
  method Data_t get() ;

  // a way to take the data out of the module (fifo)
  method ActionValue#(Data_t) takeit() ;

endinterface




//
(* synthesize *)
// an example module using a Fifo at the end of the pipe.
// in my opinion this is the only version of bsv code which produces
// good working hardware.
module mktestpush_fifo( Pusher );

   // instantiate a fifo as a "sink" at the end of the Push pipe
   FIFO#(Data_t) out_fifo_ifc() ;
   mkFIFO i_out_fifo(out_fifo_ifc) ;

   // The FIFO interface must be converted to Push Interface, which can be
   // done with the library function fifoToPush
   Push#(Data_t) pu_ifc = fifoToPush( out_fifo_ifc ) ;


   // The qbuffered function can be be changed to buffered or passed
   // qbuffered inserts a fifo, and buffered a register, 
   // and passed inserts nothing.
   // The sink interface -- pu_ifc -- is tagged at the end of the chain.
   // Using the monadic binding operator "<-" 
   Push#(Data_t) mkadd;
   mkadd <- ( pipe(qbuffered(add2),
                   qbuffered(add2,pu_ifc)));
   // synthesis result is fifo -> add -> fifo -> add -> out_fifo

   // The qbuffered function wraps the function "add2" in Push interface with a 2 element
   //   fifo on the up stream side
   // The pipe function combines connects two streams, but does not add any hardware


   // Another variation with only 1 pipe stage. 
   //   the function passed is used instead of qbuffered which wraps the function on
   // synthesis result is add2 -> fifo -> add2 -> out_fifo
   // mkadd <- ( pipe(passed(add2), qbuffered(add2,pu_ifc)));

   // result is fifo -> add2 -> add2 -> out_fifo
   // mkadd <- ( pipe(qbuffered(add2), passed(add2,pu_ifc)));  
   
   // Input to start the pipeline
   method go( in2 );
   action
      mkadd.push( in2 ) ;
   endaction
   endmethod

   // peek at the value in the fifo sink -- the output fifo
   method get ();
     return out_fifo_ifc.first ;
   endmethod

   // dequeues the data from fifo sink
   method takeit();
   actionvalue
     out_fifo_ifc.deq() ;
     return out_fifo_ifc.first();
   endactionvalue
   endmethod
     
endmodule // testpush


//
(* synthesize *)
// A modification of the above module.
// This pipelines operation with registers rather than fifos,
// thus producing less hardware, but the generated Verilog is incorrect --
// the enqueuing operation does not consider the initial latency thru 
// the pipeline, and the pipeline only advances when the chain is pushed.
// One may use loopy fifos (next module), instead of buffers, but this produces designs with
// long chains, i.e., the RDY_go signal look at each loopy fifo.
// Using a Maybe data type through the pipe will allow better handling of stall cycles.
module mktestpush_fifo_wreg( Pusher );

   FIFO#(Data_t) fifo_ifc() ;
   mkFIFO i_fifo(fifo_ifc) ;

   Push#(Data_t) pu_ifc = fifoToPush( fifo_ifc ) ;

   // use buffered instead of qbuffered function.
   Push#(Data_t) mkadd <- ( pipe(buffered(add2), buffered(add2,pu_ifc)));   
   
   method go( inp );
   action
      mkadd.push( inp ) ;
   endaction
   endmethod

   method get ();
     return fifo_ifc.first() ;
   endmethod

   method takeit();
   actionvalue
     fifo_ifc.deq() ;
     return fifo_ifc.first();
   endactionvalue
   endmethod
     
   
endmodule // testpush

//
//(* synthesize *)
// A modification of the above module.
// This pipelines operation with single element fifos
// thus producing less hardware
// The down side is that may be long cycle time since the queue enable must
// look at the full/empty state of all fifos in the pipe.
module mktestpush_fifo_loopy( Pusher );

   FIFO#(Data_t) fifo_ifc() ;
   mkFIFO i_fifo(fifo_ifc) ;

   Push#(Data_t) pu_ifc = fifoToPush( fifo_ifc ) ;

   // use buffered instead of qbuffered function.
   Push#(Data_t) mkadd <- ( pipe(q1buffered(add2), q1buffered(add2,pu_ifc)));   
   
   method go( inp );
   action
      mkadd.push( inp ) ;
   endaction
   endmethod

   method get ();
     return fifo_ifc.first() ;
   endmethod

   method takeit();
   actionvalue
     fifo_ifc.deq() ;
     return fifo_ifc.first();
   endactionvalue
   endmethod
     
   
endmodule // testpush


//
(* synthesize
*)
// A module with a register as the sink
// Note that there is no hand shaking w.r.t. to pushing data into
// the stream, and hence data may be lost.
//  Also the fifo with regs, the pipeline only advances when
// data is pushed.   The generated verilog is not very useful unless
// the designer always_enable this, and the latency is clearly understood.
// Using a Maybe data type through the pipe will allow better handling of stall cycles.
module mktestpush_reg( Pusher );

   Reg#(Data_t) reg_ifc() ;
   mkReg#(0) i_reg(reg_ifc) ;

   // Use the library function regToPush to convert the Reg interface to a Push
   Push#(Data_t) pu_ifc = regToPush( reg_ifc ) ;

   Push#(Data_t) mkadd <- ( pipe(buffered(add2), buffered(add2,pu_ifc)));
   
   
   method go( inp );
   action
      mkadd.push( inp ) ;
   endaction
   endmethod

   method get ();
     return reg_ifc ;
   endmethod

   method takeit();
   actionvalue
     return reg_ifc;
   endactionvalue 
   endmethod 
   
endmodule // testpush


(* synthesize *)
// A final version with uses the RWire model and hence is purely combinational.
// In this example we are using the "passed" function from the Push library
// compose both add2 functions.
// This is not a recommended method, as the compose function provides the same functionality.
module mktestpush_rwire( Pusher );

   RWire#(Data_t) rw_ifc() ;
   mkRWire i_reg(rw_ifc) ;

   // There is not a library function to convert a from a RWire interface
   // into a Push interface, but this can be done as follows.
   Push#(Data_t) pu_ifc =  (interface Push ;
                                  method push( x ) ; 
                                  action rw_ifc.wset( x ) ; endaction
                                  endmethod:push 
                                  endinterface   );


   Push#(Data_t) mkadd <- pipe(passed(add2), passed(add2,pu_ifc));
   

   method go( inp );
   action
      mkadd.push( inp ) ;
   endaction
   endmethod

   method get() ;
     return validValue( rw_ifc.wget() ) ;
   endmethod

   method takeit() ;
   actionvalue
     return validValue( rw_ifc.wget() ) ;
   endactionvalue 
   endmethod

endmodule // testpush



// parameterized module -- a common module for testing all pipelines
module push_tester#(Pusher mypush) ( Empty );

   // a counter for simulation
   Reg #(Bit#(16)) count();
   mkReg #(0) i_counter(count);

   // a lfsr for random patterns 
   LFSR #(Bit#(16)) lfsr();
   mkLFSR_16 i_rand(lfsr) ;

   // Start dumping
   rule init (count == 0);
     $dumpvars() ;
   endrule

   // keep counting  
   rule count_rule ;
     count <= count + 1;
     lfsr.next ;
   endrule 

   // finish simulation
   rule stop (count > 300 ); 
     $finish(0) ;
   endrule 


   // push at random times 
   // lfsr ranges from 1 to 255 so probability can be adjusted
   rule pushit (lfsr.value() > 128 ) ; 
     mypush.go( count[3:0] );
     Bit#(64) t <- $time();
     $display( "%t -- pushit %h", t, count[3:0] ) ;   
   endrule
    
   // A rule to dequeue the data
   rule pullin ( (lfsr.value() >> 8) > 128 ) ; 
     Data_t theData <- mypush.takeit( );
     Bit#(64) t <- $time();
     $display( "%t --               pull %h", t, theData ) ;   
   endrule
     
endmodule // push_tester


// sys modules are use as test bench driver

(* synthesize *)
module sys_fifo( Empty );

   Pusher dut1();
   mktestpush_fifo i_dut1(dut1);

   Empty i1() ;   
   push_tester #(dut1) tester1(i1);
   
   
endmodule // push_tester_fifo

(* synthesize *)
module sys_fifo_loopy( Empty );

   Pusher dut2();
   mktestpush_fifo_loopy i_dut2(dut2);

   Empty i2() ;   
   push_tester #(dut2) tester2(i2);
   
   
endmodule // push_tester_fifo



endpackage


import Interfaces :: * ;
import FIFO :: * ;
import FIFOF :: * ;
import GetPut :: * ;
import LFSR :: * ;

(* synthesize *)
module mkMaster ( Master );

   String id = "T" ;
   // A counter to show that we are alive and to generate addresses
   Reg#(Bit#(28)) counter <-  mkReg(0) ;

   // An LFSR for random addresses
   LFSR #(Bit#(4)) random <- mkRCounter( 0 ) ; // for debug
   //LFSR #(Bit#(4)) random <-  mkLFSR_4 ; // for pseudo random numbers
   
   // a register for the request data  use unguarded fifo to allow idle requests!
   FIFOF#(BusRequest) requestData <- mkUGFIFOF ;

      // Rule to start the simulation and turn on vcd dumps
   rule init ( counter == 0 ) ;
      $dumpvars() ;
      $dumpon() ;
      counter <= 1 ;
   endrule

   // rule to end the simulations
   rule count (counter > 0 )  ;
      random.next;
      counter <= counter + 1;
      if ( counter > 50 )  $finish(0) ; 
   endrule
   
   // rule to generate new request data
   rule newdata ((random.value <= 4'd7 ) && (requestData.notFull)) ;
     
      let high = random.value ;       // grab a 4 bit random number
      let reqaddr = {high, counter };
      requestData.enq( BusRequest {addr:reqaddr, data:1, read_write:Read } ) ;

      // $display ( "enqueing data %h", reqaddr ) ;
      // Question: if the counter is used for a random value why is 7 not queued?
               
   endrule

   
   // Let the master know that a grant was received
   RWire#(Bool)  r_granted <- mkRWire ;

   // Keeps track if the master has send an idle transaction.
   Reg#(Bool) idleSent <- mkReg( True );

   //  Send out a request for bus access
   method ActionValue#(Bool) m_bus_request();
      // We always want the bus if there is a request in the Q
      return requestData.notEmpty;
   endmethod

   // See if bus access has been granted 
   method  Action m_bus_grant( bus_grant ) ;
      r_granted.wset( bus_grant ) ;
   endmethod

   // method when bus has a response to this master.
   interface Put m_response ;
      method Action put( response ) ;
         // Queue the response 
         if ( ! idleSent )
            begin
               $display( "response %s: counter: %0d  stat: %h, data: %h", id,
                        counter, response.status, response.data ) ;
            end
         
      endmethod
   endinterface

   // Sending out a transaction request to the bus
   interface Get m_request;
      // conditional on bus access being granted.
      method ActionValue#(BusRequest) get() if (r_granted.wget matches tagged Valid True ) ;

         let reqData = dummyRequest ;

         // Decide on a regular or idle transaction
         if ( requestData.notEmpty )
            begin
               reqData = requestData.first ;          requestData.deq ;
               idleSent <= False ;
               reqData.addr = modAddress( reqData, counter ) ;
               $display( "sending request %s -- %0d %h %h %b", id,
                        counter, reqData.addr, reqData.data, reqData.read_write) ;

            end
         else
            begin
               reqData = idleRequest ;
               idleSent <= True ;
            end

         return reqData ; 
      endmethod
   endinterface
   
endmodule

// a function to add a time stamp/counter to the transaction address.
function BusAddr modAddress( BusRequest reqin, Bit#(28) cntr );
   let newAddr = { reqin.addr[31:28], cntr} ;
   return newAddr ;
endfunction

// ///////////////////////////////////////////////////////////////////////////      
// a parameterized master.
// Note that this cannot be synthezied to Verilog, only via a top level wrapper
module mkMasterP#(Bit#(28) finish, Bit#(4) seed, String id)  ( Master );

   // A counter to show that we are alive and to generate addresses
   Reg#(Bit#(28)) counter <-  mkReg(0) ;

   // An LFSR for random addresses
   // LFSR #(Bit#(4)) random <- mkRCounter( 0 ) ; // for debug
   LFSR #(Bit#(4)) random <-  mkLFSR_4 ; // for pseudo random numbers
   
   // a register for the request data  use unguarded fifo to allow idle requests!
   FIFOF#(BusRequest) requestData <- mkUGFIFOF ;

      // Rule to start the simulation and turn on vcd dumps
   rule init ( counter == 0 ) ;
      $dumpvars() ;
      $dumpon() ;
      random.seed( seed ) ;
      counter <= 1 ;
   endrule

   // rule to end the simulations
   rule count ( counter > 0 ) ;
      random.next;
      counter <= counter + 1;
      if ( counter > finish )  $finish(0) ; 
   endrule
   
   // rule to generate new request data
   rule newdata ((random.value <= 4'd7 ) && (requestData.notFull)) ;
     
      let high = random.value ;       // grab a 4 bit random number
      
      let reqaddr = {high, counter };
      requestData.enq( BusRequest {addr:reqaddr, data:1, read_write:Read } ) ;

   endrule

   
   // Let the master know that a grant was received
   RWire#(Bool)  r_granted <- mkRWire ;

   // Keeps track if the master has send an idle transaction.
   Reg#(Bool) idleSent <- mkReg( True );

   //  Send out a request for bus access
   method ActionValue#(Bool) m_bus_request();
      // We always want the bus if there is a request in the Q
      return requestData.notEmpty;
   endmethod

   // See if bus access has been granted 
   method  Action m_bus_grant( bus_grant ) ;
      r_granted.wset( bus_grant ) ;
   endmethod

   // method when bus has a response to this master.
   interface Put m_response ;
      method Action put( response ) ;
         // Queue the response 
         if ( ! idleSent )
            begin
               $display( "response %s: counter: %0d  stat: %h, data: %h", id,
                        counter, response.status, response.data ) ;
            end
         
      endmethod
   endinterface

   // Sending out a transaction request to the bus
   interface Get m_request;
      // conditional on bus access being granted.
      method ActionValue#(BusRequest) get() if (r_granted.wget matches tagged Valid True ) ;

         let reqData = dummyRequest ;

         // Decide on a regular or idle transaction
         if ( requestData.notEmpty )
            begin
               reqData = requestData.first ;          requestData.deq ;
               idleSent <= False ;
               reqData.addr = modAddress( reqData, counter ) ;
               $display( "sending request %s -- %0d %h %h %b", id,
                        counter, reqData.addr, reqData.data, reqData.read_write) ;

            end
         else
            begin
               reqData = idleRequest ;
               idleSent <= True ;
            end

         return reqData ; 
      endmethod
   endinterface
   
endmodule



// ///////////////////////////////////////////////////////////////////////////      
(* synthesize *)
module mkMaster_500_1 (Master ) ;
   Master localM <- mkMasterP(500,1, "A" ) ;
   return localM ;
endmodule

(* synthesize *)
module mkMaster_500_6 (Master ) ;
   Master localM <- mkMasterP(500,6, "B") ;
   return localM ;
endmodule

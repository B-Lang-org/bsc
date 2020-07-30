// Slave Modules for AMBA bus
import FIFO :: * ;
import GetPut :: * ;
import Interfaces :: * ;


(* synthesize *)
// A default slave which does nothing but always returns an OK status
module defaultSlave( Slave ) ;

   // sub-interface for bus to place a request.
   interface Put s_request ;
      method Action put( req ) ;
         // This method is always ready
      endmethod
   endinterface

   // sub-interface for bus to get a response. 
   interface Get s_response ;
      method ActionValue#(BusResponse) get () ; 
         return defaultResponse ;
      endmethod
   endinterface
endmodule

// ///////////////////////////////////////////////////////////////////////////
(* synthesize *)
// A slave with reponds OK on the next cycle
// and sends back the request address on the data bus
module mkSlave1( Slave );

   // A fifo to hold the request
   FIFO#(BusRequest) requestQ <- mkFIFO ;

   // Enqueue a request when the bus puts one to the slave
   interface Put s_request ;
      method Action put( request );
         requestQ.enq( request ) ;
      endmethod
   endinterface

   
   interface Get s_response ;
      method ActionValue#(BusResponse) get() ;
         // The implicit RDY condition is there must be something in requestQ
         let req = requestQ.first ;  requestQ.deq ;
         let addr = req.addr;
         // transfer address to data 
         let resp = BusResponse{ data:addr, status:OK } ;
         return resp ;
      endmethod
   endinterface
   
endmodule

// ///////////////////////////////////////////////////////////////////////////
(* synthesize *)
// A slave with reponds OK after 1 cycle latency
module mkSlave2( Slave );

   // create 2 fifos to delay the result
   FIFO#(BusRequest) requestQ0 <- mkFIFO ;
   FIFO#(BusRequest) requestQ1 <- mkFIFO ;

   // Rule to pass data from first fifo to second.
   rule delay ;
      requestQ1.enq( requestQ0.first ) ;
      requestQ0.deq ;
   endrule
   
   // When the bus puts a request to the slave, then enqueue it.
   // The bus logic ensure that only one request is ever pending.
   interface Put s_request ;
      method Action put( request ) ;
         requestQ0.enq( request ) ;
      endmethod
   endinterface

   // The bus can only get a response after the delay of the 2 queues
   interface Get s_response ;
      method ActionValue#(BusResponse) get() ;
         let req = requestQ1.first ;  requestQ1.deq ;
         let addr = req.addr;
         let resp = BusResponse{ data:addr, status:OK } ;
         return resp ;
      endmethod
   endinterface
   
endmodule

// ///////////////////////////////////////////////////////////////////////////
// Create a slave which has a run time configurable delay takedn from the data
// portion of the request.  The counter is limited to a 4 bit delay -- 15 cycles.
(* synthesize *)
module mkSlaveN( Slave ) ;

   Reg#(Bit#(4)) counter <- mkReg( 0 ) ;
   Reg#(BusAddr) oldAddr <- mkReg( 0 ) ;

   // Count down if the counter is not 0
   rule countDown ( counter > 0 ) ;
      counter <= counter - 1 ;
   endrule

   
   interface Put s_request ;
      method Action put( BusRequest request );
         // Set the counter and save the address.
         counter <= truncate( request.data ) ;
         oldAddr <= request.addr ;
      endmethod
   endinterface

   interface Get s_response ;
      method ActionValue#(BusResponse) get () if ( counter == 0 );
         let resp = BusResponse{ data:oldAddr, status:OK } ;
         return resp;
      endmethod
   endinterface
   
endmodule

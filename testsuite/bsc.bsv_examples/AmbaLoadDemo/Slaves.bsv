// Slave Modules for AMBA bus
import FIFO :: * ;
import GetPut :: * ;
import Interfaces :: * ;


// Create a slave which has a run time configurable via parameter delayCntr
// The counter is limited to a 4 bit delay -- 15 cycles.
//(* synthesize *)
module mkSlave#(Bit#(4) delayCntr )( Slave ) ;

   Reg#(Bit#(4)) counter <- mkReg( 1 ) ;
   Reg#(BusAddr) oldAddr <- mkReg( 0 ) ;

   // Count down if the counter is not 0
   rule countDown ( counter > 1 ) ;
      counter <= counter - 1 ;
   endrule

   
   interface Put s_request ;
      // only accpet request when counter is 1
      method Action put( BusRequest request ) if (counter == 1);
         // Set the counter and save the address.
         counter <= delayCntr ;
         oldAddr <= request.addr ;
      endmethod
   endinterface

   interface Get s_response ;
      method ActionValue#(BusResponse) get () if ( counter == 1 );
         let resp = BusResponse{ data:oldAddr, status:OK } ;
         return resp;
      endmethod
   endinterface
   
endmodule



// //////////////////////////////////////////////////////////////////////////
// Create a slave which has a run time configurable delay takedn from the data
// portion of the request.  The counter is limited to a 4 bit delay -- 15 cycles.
//(* synthesize *)
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

// /////////////////////////////////////////////////////////////////////////
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


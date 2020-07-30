import Interfaces :: * ;
import GetPut :: * ;
import Vector :: * ;

// Define some slave select functions

// Function to create a 2 bit one-hot result to selct the slave
function Bit#(2) slaveSel2( BusAddr addr );
   Bit#(4) selbit = addr[31:28] ;
   Bit#(2) result = 0 ;
   case ( selbit )
      4'b0000,
      4'b0001,
      4'b0010,
      4'b0011: result = 2'b01 ;
      4'b0100,
      4'b0101,
      4'b0110,
      4'b0111: result = 2'b10 ;
      default: result = 0 ;     // default slave 
   endcase
   return result ;
endfunction

// Function to create a 2 bit one-hot slave results
function Bit#(2) slaveSel3( BusAddr addr );
   Bit#(1) selbit = addr[31] ;
   Bit#(2) result = ( addr == idleAddress) ? 2'b00 :
                    (0 == selbit) ?  2'b01 : 2'b10 ;
   return result ;
endfunction



// // Function with returns a SlaveSide interface for a given address and set of 
//  RWires corresponding to select, request, and response bits.
// This function avoids the cut-n-paste style from above.      
function BusSlaveSide mkSlaveIfc(
                                 Bit#(size)  addr,
                                 Bit#(size)  lastSelect,
                                 Bit#(size)  select,
                                 BusRequest  request,
                                 RWire#(BusResponse) response );
   return    (
   interface BusSlaveSide ;
      interface Get bs_request ;
         method ActionValue#(BusRequest) get() if ( select == addr ) ;
              return request ;
         endmethod
      endinterface
      interface Put bs_response ;
         method Action put( res ) if ( lastSelect == addr ) ;
              response.wset( res ) ; 
         endmethod
      endinterface
   endinterface ) ;
endfunction

      
// ///////////////////////////////////////////////////////////////////////////
module bus_1m_2s #(function Bit#(2) slaveDecode ( BusAddr a ) ) ( B1m2s );
         
   RWire#(BusRequest)  request  <- mkRWire ;
   let realRequest = fromMaybe( dummyRequest, request.wget ) ;
   let addr = realRequest.addr ;
   let slaveSelect =  isValid( request.wget) ? slaveDecode( addr ) : 0 ;

   RWire#(BusResponse) response <- mkRWire ;

   Reg#(Bit#(2) )      lastSlaveSel <- mkReg( 0 ) ;

   rule lastSlaveUpdate ( isValid( response.wget ) ) ;
      lastSlaveSel <= slaveSelect ;
   endrule

   interface BusMasterSide ms0 ;
      // Single master is always granted bus
      method Action bms_bus_request( request );
      endmethod

      method ActionValue#(Bool) bms_bus_grant ();
         return True ;
      endmethod
      
      interface Put bms_request;
          method Action put( req ) if ( isValid( response.wget )) ;
             request.wset( req ) ;
          endmethod   
      endinterface
      interface Get bms_response ;
         method ActionValue#(BusResponse) get ()  if (isValid ( response.wget )) ;
            return fromMaybe( errorResponse, response.wget ) ;
         endmethod
      endinterface
   endinterface
   
   interface defSlave = mkSlaveIfc( 2'b00, lastSlaveSel, slaveSelect, realRequest, response ) ; 
   interface ss0      = mkSlaveIfc( 2'b01, lastSlaveSel, slaveSelect, realRequest, response ) ;
   interface ss1      = mkSlaveIfc( 2'b10, lastSlaveSel, slaveSelect, realRequest, response ) ;

endmodule
      

      
// ///////////////////////////////////////////////////////////////////////////
module bus_2m_2s #(function Bit#(2) slaveDecode ( BusAddr a ) ) ( B2m2s );

   // One bus request per master
   RWire#(Bool)   m0_bus_request <- mkRWire ;
   RWire#(Bool)   m1_bus_request <- mkRWire ;

   // One-hot grant logic
   Vector#(2,Bool)  masterGrant = selectMaster2( m0_bus_request.wget, m1_bus_request.wget ) ;

   // One transaction request per master
   RWire#(BusRequest)   request <- mkRWire ;

   BusRequest realRequest = fromMaybe( dummyRequest, request.wget ); 
   BusAddr addr = realRequest.addr ;
   Bit#(2) slaveSelect = slaveDecode( addr );

   // Bus Response
   RWire#(BusResponse)  response <- mkRWire ;

   BusResponse real_response = fromMaybe( errorResponse, response.wget ) ;
   Bool response_complete = isValid( response.wget ) ;

   Reg#(Vector#(2,Bool)) lastMaster <- mkReg( unpack( 2'b01 ) ) ;
   Reg#(Bit#(2) )      lastSlaveSel <- mkReg( 0 ) ;
   
   rule nextAddressPhase (response_complete) ;
      lastMaster <= masterGrant ;
      lastSlaveSel  <= slaveSelect ;
      
   endrule
   
   
   interface ms0 = mkMasterIfc( m0_bus_request, request, response_complete, real_response, masterGrant[0], lastMaster[0] ) ;
   interface ms1 = mkMasterIfc( m1_bus_request, request, response_complete, real_response, masterGrant[1], lastMaster[1] ) ;      
   interface defSlave = mkSlaveIfc( 2'b00, lastSlaveSel, slaveSelect, realRequest, response ) ; 
   interface ss0      = mkSlaveIfc( 2'b01, lastSlaveSel, slaveSelect, realRequest, response ) ;
   interface ss1      = mkSlaveIfc( 2'b10, lastSlaveSel, slaveSelect, realRequest, response ) ;

   
endmodule
     


// ///////////////////////////////////////////////////////////////////////////      
function BusMasterSide mkMasterIfc(
                                   RWire#(Bool)         r_bus_request,
                                   RWire#(BusRequest)   mrequest,
                                   Bool                 response_complete,
                                   BusResponse          response,
                                   Bool                 masterSelected,
                                   Bool                 lastMasterSelected
                                   );
   return (
           interface BusMasterSide;
              method Action bms_bus_request ( request );
                 r_bus_request.wset( request );
              endmethod

              method ActionValue#(Bool) bms_bus_grant () ;
                 return masterSelected ;
              endmethod

              interface Put bms_request ;
                 method Action put( req ) if ( response_complete && masterSelected ) ;
                    mrequest.wset( req ) ;
                 endmethod
              endinterface

              interface Get bms_response ;
                 method ActionValue#(BusResponse) get () if ( response_complete && (lastMasterSelected) );
                    return response ;
                 endmethod
              endinterface
           endinterface
           ) ;
endfunction
      
// ///////////////////////////////////////////////////////////////////////////      
// decoding for the master
function Vector#(2,Bool) selectMaster2( Maybe#(Bool) m0, Maybe#(Bool) m1 ) ;
   let result = (fromMaybe( False, m0 )) ? 2'b01 :
                 (fromMaybe( False, m1 )) ? 2'b10 :
                 2'b01 ;
   return unpack ( result );
endfunction

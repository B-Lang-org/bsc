import Interfaces :: * ;
import GetPut :: * ;
import Vector :: * ;

// Function to create a 2 bit one-hot results
// TODO: try to use OInt type
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
      default: result = 0 ;
   endcase
   return result ;
endfunction



// ///////////////////////////////////////////////////////////////////////////      
(* synthesize *)
module bus_1m_1s ( B1m1s );

   // Rwire and functions for request/grant logic
   RWire#(Bool)        m0_busRequest <- mkRWire ;

   let m0_grant = True ;       // Always grant the bus

   // Rwire and functions for request and slaveSelect
   RWire#(BusRequest)  request  <- mkRWire ;

   BusRequest realRequest = fromMaybe( dummyRequest, request.wget ); 
   BusAddr addr = realRequest.addr ;
   Bit#(2) slaveSelect = slaveSel2( addr ) & 2'b01 ;
   
   // Rwire and functions for response (from slave
   RWire#(BusResponse) response <- mkRWire ;

   BusResponse realResponse = fromMaybe( errorResponse, response.wget ) ;
   Bool responseComplete = isValid( response.wget ) ;

   // register to hold 
   Reg#(Bit#(2) )      lastSlaveSel <- mkReg( 0 ) ;
   
   rule lastSlaveUpdate ( responseComplete ) ;
      lastSlaveSel <= slaveSelect ;
   endrule
   
   interface BusMasterSide ms0 ;
      // Single master is always granted bus
      method Action bms_bus_request( req );
         m0_busRequest.wset( req ) ;
      endmethod
      method ActionValue#(Bool) bms_bus_grant ();
         return m0_grant ;
      endmethod
      
      interface Put bms_request;
          method Action put( transRequest ) if (responseComplete ) ;
             request.wset( transRequest ) ;
          endmethod   
      endinterface
      interface Get bms_response ;
         method ActionValue#(BusResponse) get () if ( responseComplete ) ;
            return realResponse ;
         endmethod
      endinterface
   endinterface


   interface BusSlaveSide ss0 ;
      interface Get bs_request ;
         method ActionValue#(BusRequest) get() if ( slaveSelect == 2'b01) ;
            return realRequest ;
         endmethod
      endinterface
      interface Put bs_response ;
         method Action put( res ) if (lastSlaveSel == 2'b01 );
           response.wset( res ) ; 
         endmethod
      endinterface
   endinterface

   
   interface BusSlaveSide defSlave ;
      interface Get bs_request ;
         method ActionValue#(BusRequest) get() if ( slaveSelect != 2'b01 ) ;
            return realRequest ;
         endmethod
      endinterface
      
      interface Put bs_response ;
         method Action put( res ) if ( lastSlaveSel != 2'b01 ) ;
           response.wset( res ) ; 
         endmethod
      endinterface
   endinterface
   

endmodule

// ///////////////////////////////////////////////////////////////////////////
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
(* synthesize *)
module bus_1m_2s ( B1m2s );
         
   RWire#(BusRequest)  request  <- mkRWire ;
   let realRequest = fromMaybe( dummyRequest, request.wget ) ;
   let addr = realRequest.addr ;
   let slaveSelect =  isValid( request.wget) ? slaveSel2( addr ) : 0 ;

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


function BusMasterSide mkMasterIfc(
                                   RWire#(Bool)         r_bus_request,
                                   RWire#(BusRequest)   mrequest,
                                   Bool                 response_complete,
                                   BusResponse          response,
                                   Bool                 masterSelected,
                                   Bool                 lastMasterSelected
                                   );
   return (
           interface BusMasterSide ;
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

// function BusRequest selectRequest2( Bit#(2) sel, RWire#(BusRequest) m0, RWire#(BusRequest) m1 ) ;
//    BusRequest result ;
//    case (sel )
//       2'b01: result = fromMaybe( errorRequest, m0.wget ) ;
//       2'b01: result = fromMaybe( errorRequest, m1.wget ) ;
//       default: result = errorRequest ;
//    endcase
//    return result ;
// endfunction
      
// ///////////////////////////////////////////////////////////////////////////      
(* synthesize *)  
module bus_2m_2s( B2m2s );

   // One bus request per master
   RWire#(Bool)   m0_bus_request <- mkRWire ;
   RWire#(Bool)   m1_bus_request <- mkRWire ;

   // One-hot grant logic
   Vector#(2,Bool)  masterGrant = selectMaster2( m0_bus_request.wget, m1_bus_request.wget ) ;

   // One transaction request per master
   RWire#(BusRequest)   request <- mkRWire ;

   BusRequest realRequest = fromMaybe( dummyRequest, request.wget ); 
   BusAddr addr = realRequest.addr ;
   Bit#(2) slaveSelect = slaveSel2( addr );

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

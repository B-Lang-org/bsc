// TODO
//   have slaves look at transfer type for idle.
//   hmost is a fixex 4 bits??

import ConfigReg :: * ;
import Connectable:: * ;
import FIFOF :: * ;
import OInt :: * ;
import Vector :: * ;

// Definitions for Address and Data Widths.
typedef Bit#(32) BusAddr ;
typedef Bit#(32) BusData ;

//  Enum for the bus transfer type
typedef enum { Write, Read
              } RW 
deriving (Bits,Eq) ;

typedef enum { IDLE, BUSY, NONSEQ, SEQ
              } TransferType
deriving ( Bits, Eq) ;

// structure to describe the bus request 
typedef struct {
                TransferType   trans ;
                RW       read_write;
                BusData  data;
                BusAddr  addr;
                } BusRequest
deriving(Bits);

typedef struct {
                TransferType   trans ;
                RW       read_write;
                BusAddr  addr;
                } AddrPhaseRequest
deriving(Bits);

// Define a default request variables
BusRequest dummyRequest = BusRequest{
                                     trans: NONSEQ ,
                                     addr: 'hdead_add0 ,
                                     data: 'hdead_da1a ,
                                     read_write: Read } ;
AddrPhaseRequest dummyRequestAP = AddrPhaseRequest{
                                                   trans: IDLE,
                                                   addr: 'hdead_add0 ,
                                                   read_write: Read } ;
BusAddr idleAddress = 'hFFFF_FFF0 ;
BusRequest  idleRequest = BusRequest{
                                     trans: IDLE ,
                                     addr: idleAddress ,
                                     data: 'hFFFF_FFFF ,
                                     read_write: Read } ;

// An enum type for bus transaction return status
typedef enum { OK, Error, Retry, Split }  BusStat
	deriving ( Bits ) ;

// structure to describe the bus response.  The data maybe unused (e.g. writes)
typedef struct {
                BusStat  status;
                BusData  data;
                } BusResponse
deriving(Bits);
// Define a dummy response with error status
BusData errorResponseData = 'hdead_badd ; 
BusResponse errorResponse = BusResponse{ data: errorResponseData, 
                                        status: Error } ;
BusData  defaultResponseData = 32'hdef0_def0 ;
BusResponse defaultResponse = BusResponse{ data: defaultResponseData, 
                                           status: OK } ;


// ///////////////////////////////////////////////////////////////////////////
// The Master Interface for Amba bus
interface Master ;

   method Bool hbusreq() ;
      // hbusreq sends a request to access to the bus

   method Action hgrant( ) ;
      // hgrant is an input received from the bus to show if the bus 
      // request has been granted.

   method TransferType htrans() ;
   method BusAddr haddr() ;
   method RW hwrite() ;
      // request method provides the bus a way to get the request

   method BusData hwdata() ;
      // hwdata is the data out for the transaction.
            
   method Action hready ( BusData hrdata, BusStat hresp ) ;
      // hready provides the bus a place to put the response.
endinterface


// The bus provides a BusMasterSide interface for each master it connects.
interface BusMasterSide ;
   method Action bmsBusRequest ();
      // Takes a bus request input from the master  Action implies request

   method Bool bmsBusGrant ();
      // returns the bus grant to the master

   method Action bmsRequest ( BusAddr haddr, RW hwrite, TransferType htrans ) ;
      // A method for the Master to place the request.
      
   method Action bmsData( BusData hwdata ) ;
      // Data out
      
   method ActionValue#(BusResponse) hrdata ()  ;
      // A method for the Master to set a response.  AV needed
endinterface


      
// ///////////////////////////////////////////////////////////////////////////
// Slave and Bus Slave Side interfaces
// These are similar to the Master and MasterSide interface, except no bus request/grant
// are needed.
interface Slave ;
   method Action hsel( BusAddr haddr, RW hwrite, TransferType htrans ) ;
      // a place for the bus to put a request -- the action indicated Addr is ready.

   method Action dataPhase( BusData hwdata) ;
      // data comes over later.
      
//   method  ActionValue#(BusResponse) hresp();
   method Bool hready() ;
   method BusData hrdata() ;
   method BusStat hresp() ;

endinterface


interface BusSlaveSide ;
   method ActionValue#(AddrPhaseRequest) bsRequest ;
      // a place for the slave to get a request

   method BusData bsData () ;
      
   method Action bsResponse( BusData hrdata, BusStat hresp ) ;
      // a place the the slave to put a response
endinterface



// ///////////////////////////////////////////////////////////////////////////
// Connectables describe the module needed to connect two interfaces
// 
instance Connectable#(Master, BusMasterSide) ;
      module mkConnection#(Master m, BusMasterSide b ) (Empty) ;
         // a rule to transfer the request from the master to the bus
         (* no_implicit_conditions, fire_when_enabled *)
         rule connectMasterBusReq (m.hbusreq) ;
            b.bmsBusRequest( ) ;
         endrule
         
         // A rule to transfer the grant from the bus to the master.
         (* no_implicit_conditions, fire_when_enabled *)
         rule connectMasterBusGrant (b.bmsBusGrant) ;
            m.hgrant() ;
         endrule

         rule connectMasterRequest ;
            b.bmsRequest( m.haddr, m.hwrite, m.htrans ) ;
         endrule

         rule connectMasterData ;
            b.bmsData( m.hwdata ) ;
         endrule
         
         rule connectMasterResponse ;
            BusResponse r <- b.hrdata ;
            m.hready( r.data, r.status ) ;
         endrule
      endmodule
endinstance

// Provide another mkConnection for the Master side with arguments reversed.      
instance Connectable#(BusMasterSide, Master) ;
      module mkConnection#(BusMasterSide b, Master m ) (Empty) ;
         mkConnection( m, b );
      endmodule
endinstance

// Define the connection between a Slave and BusSideSlave interfaces
instance Connectable#(Slave, BusSlaveSide) ;
      module mkConnection#(Slave s, BusSlaveSide b ) (Empty) ;

         rule connectSlaveRequest ;
            AddrPhaseRequest r <- b.bsRequest ;
            s.hsel( r.addr, r.read_write, r.trans ) ;
         endrule

         rule connectSlaveResponse (s.hready )  ;
            b.bsResponse( s.hrdata, s.hresp ) ;
         endrule

         (* no_implicit_conditions, fire_when_enabled *)
         rule connectSlaveData ;
            s.dataPhase( b.bsData ) ;
         endrule
      endmodule
endinstance

// Provide another mkConnection for the Slave side with arguments reversed. 
instance Connectable#(BusSlaveSide, Slave) ;
      module mkConnection#(BusSlaveSide b, Slave s ) (Empty) ;
         mkConnection( s, b ) ;
      endmodule
endinstance



interface BusParam#(type mas, type slv ) ;
   interface Vector#(mas, BusMasterSide)  ms ;
   interface Vector#(slv, BusSlaveSide) ss ;

   interface BusSlaveSide defSlave ;
endinterface

// Ideally we want to reuse the same interface as before...
interface BlueMasterAdapter ;
   method Action read ( BusAddr address ) ;
   method Action write ( BusAddr address, BusData bdata ) ;
   method BusResponse response() ;
   method Action takeResponse () ;
endinterface

interface AmbaMasterAdapter ;
   interface BlueMasterAdapter bbus ;
   interface Master amaster ;
endinterface
      
interface BlueSlaveAdapter ;
   method BusRequest request() ;
   method Bool slaveSelect() ;
   method Action response( BusResponse response );
endinterface

interface AmbaSlaveAdapter ;
   interface BlueSlaveAdapter bbus ;
   interface Slave aslave ;
endinterface
      

// // Function with returns a SlaveSide interface for a given address and set of 
//  RWires corresponding to select, request, and response bits.
// This function avoids the cut-n-paste style from above.      
function BusSlaveSide mkSlaveIfc(
                                 Bit#(size)  addr,
                                 Bit#(size)  lastSelect,
                                 Bit#(size)  select,
                                 AddrPhaseRequest  request,
                                 BusData data ,
                                 RWire#(BusResponse) response );
   return
   (
    interface BusSlaveSide ;
       method ActionValue#(AddrPhaseRequest) bsRequest() if ( select == addr ) ;
          return request ;
       endmethod
       method BusData bsData () ;
          return data ;
       endmethod
       method Action bsResponse( hrdata, hresp ) if ( lastSelect == addr ) ;
          response.wset( BusResponse{ status:hresp, data:hrdata}  ) ; 
       endmethod
    endinterface ) ;
endfunction

     


// ///////////////////////////////////////////////////////////////////////////      
function BusMasterSide mkMasterIfc(
                                   RWire#(Bool)         r_bus_request,
                                   RWire#(AddrPhaseRequest)   mrequest,
                                   RWire#(BusData)      mdata,
                                   Bool                 response_complete,
                                   BusResponse          response,
                                   Bool                 masterSelected,
                                   Bool                 lastMasterSelected
                                   );
   return (
           interface BusMasterSide ;
              method Action bmsBusRequest ( );
                 r_bus_request.wset( True );
              endmethod

              method Bool bmsBusGrant () ;
                 return masterSelected ;
              endmethod

              method Action bmsRequest( haddr, hwrite, htrans )  if ( response_complete && masterSelected ) ;
                 mrequest.wset( AddrPhaseRequest{ trans:htrans, addr:haddr, read_write:hwrite} ) ;
              endmethod
              method Action bmsData( data ) if ( lastMasterSelected ) ;
                 mdata.wset( data ) ;
              endmethod

              method ActionValue#(BusResponse) hrdata () if ( response_complete && (lastMasterSelected) );
                 return response ;
              endmethod
           endinterface
           ) ;
endfunction
      

// A parameterize Amba Bus 
module busP#(
             parameter function Bit#(slv) slaveDecode( BusAddr a ) )
                           ( BusParam#(mas,slv ) ) ;
                          
   // One bus request per master
   Vector#(mas,RWire#(Bool)) requestsRW <- replicateM( mkRWire ) ;

   // One-hot grant logic
   OInt#(mas)  hmaster = selectMaster( (requestsRW) ) ;

   // One transaction request per master
   RWire#(AddrPhaseRequest)   request <- mkRWire ;

   AddrPhaseRequest realRequest = fromMaybe( dummyRequestAP, request.wget ); 
   BusAddr addr = realRequest.addr ;

   Bit#(slv) slaveSelect = slaveDecode( addr );

   RWire#(BusData) reqdata <- mkRWire ;
   let realdata = fromMaybe( 0, reqdata.wget ) ;
                          
   // Bus Response
   RWire#(BusResponse)  response <- mkRWire ;

   BusResponse real_response = fromMaybe( errorResponse, response.wget ) ;
   Bool response_complete = isValid( response.wget ) ;

   Reg#(OInt#(mas))      lastHMaster <- mkReg( 0 ) ;
   Reg#(Bit#(slv) )      lastSlaveSel <- mkReg( 0 ) ;
   OInt#(mas) lastMaster = toOInt( fromOInt ( lastHMaster ) ) ; // Hack for OInt
   
   Integer m ;                       
   rule nextAddressPhase (response_complete) ;
      lastHMaster <=  hmaster  ; 
      lastSlaveSel  <= slaveSelect ;

// Uncomment for debug or monitoring
      `ifdef debug_amba
      Integer m ;
      for( m = 0 ; m < valueOf( mas ); m = m + 1 ) begin
         $display( "busP  %m: requests id: %0d status: %h ", m, fromMaybe(False, requestsRW[m].wget ) ) ;
      end
      $display( "busP  %m: hmaster %b ", hmaster ) ;
      $display( "busP  %m: slaveSelect %b ", slaveSelect ) ;
      $display( "busP  %m real addr %h ", addr ) ;
      `endif
   endrule

   // Now generate the interfaces
   Vector#(mas,BusMasterSide)  masholder = newVector ; 
   for( m = 0 ; m < valueOf(mas) ; m = m + 1 )
      begin
         let mstmp =  mkMasterIfc( requestsRW[m], request, reqdata,
                                     response_complete, real_response,
                                     hmaster[m], lastMaster[m] ) ;
         masholder[m] = mstmp ; 
      end
      
   Vector#(slv,BusSlaveSide) slvholder = newVector ;
   Integer s ;
   Bit#(slv) slvAddr = 1 ;                         
   for( s = 0 ; s < valueOf( slv ) ; s = s + 1 )
      begin
         let ss0 = mkSlaveIfc( slvAddr, lastSlaveSel, slaveSelect, realRequest, realdata, response ) ;
         slvAddr = slvAddr << 1 ;
         slvholder[s] = ss0 ;
      end
                          
   interface ms = masholder ; 
   interface ss = slvholder ;
   interface defSlave = mkSlaveIfc( 0, lastSlaveSel, slaveSelect, realRequest, realdata, response ) ; 
                          
endmodule

// decoding for the master
function OInt#(n) selectMaster( Vector#(n,RWire#(Bool) ) boolsIn) 
   provisos ( Log#(n,k) ) ;
   Integer vecSize = valueOf( n ) ;
   Bit#(k) masAddr = 0 ;
   Bool found = False ;
   Integer m ;
   for( m = 0; m < vecSize; m = m + 1 )
      begin
         if ( found )
            begin
               masAddr = masAddr ;
               found = True ;
            end
         else if ( fromMaybe ( False, boolsIn[m].wget ) )
            begin
               found = True ;
               masAddr = fromInteger( m ) ;
            end
         else
            begin
               found = False ;
               masAddr = masAddr ;
            end
      end
   return toOInt( found ? masAddr : 0 ) ; 
endfunction



// /////////////////////////////////////////////////////////////////////////
// A default slave which does nothing but always returns an OK status
(* synthesize, always_ready *) 
module defaultSlave( Slave ) ;

   Reg#(TransferType) treg <- mkReg(IDLE) ;
   // sub-interface for bus to place a request.
   method Action hsel( addr, rw, trans ) ; 
      treg <= trans ;
      // This method is always ready
      // $display( "default slave called:  %h, %h %h",
      //         req.read_write, req.addr, req.data ) ;
   endmethod

   method Action dataPhase ( data ) ;
   endmethod 
   method Bool hready();
      return True ;
   endmethod
   method BusStat hresp() ;
      return ((treg == IDLE) || (treg == BUSY)) ? OK : Error  ;
   endmethod
   method BusData hrdata() ;
      return ((treg == IDLE) || (treg == BUSY)) ? defaultResponseData : errorResponseData ;
   endmethod 
endmodule


           


function AddrPhaseRequest getAddr ( BusRequest req ) ;
   begin
      return AddrPhaseRequest{ trans: req.trans, addr: req.addr, read_write: req.read_write } ; 
   end
endfunction
function BusData getData ( BusRequest req ) ;
   begin
      return req.data ;
   end
endfunction   
   
module mkBlueAmbaMaster ( AmbaMasterAdapter ) ;

   FIFOF#(BusRequest) requestData <- mkUGFIFOF ;
   FIFOF#(BusResponse) responseData <- mkUGFIFOF ;
   Reg#(Bool) idleSent <- mkConfigReg( True ) ;
   Reg#(BusData)  data <- mkReg( 0 ) ;

   let reqData = ( requestData.notEmpty ) ? requestData.first : idleRequest ;
   
   interface BlueMasterAdapter bbus ;
      method Action read( address ) if ( requestData.notFull )  ;
         requestData.enq( BusRequest{ trans: NONSEQ, addr:address, data:0, read_write: Read } ) ;
      endmethod
      
      method Action write( address, wdata ) if ( requestData.notFull )  ;
         requestData.enq( BusRequest{  trans: NONSEQ,  addr:address, data:wdata, read_write: Write } ) ;
      endmethod
   
      method BusResponse response () if ( responseData.notEmpty ) ;
         return responseData.first ;
      endmethod

      method Action takeResponse () if (responseData.notEmpty ) ;
         responseData.deq ;
      endmethod
   endinterface

   interface Master amaster ;
      method Bool hbusreq();
         return  requestData.notEmpty ;
      endmethod

      method Action hgrant ( ) ;
         // 2 cases here, since a bus can be granted even when not request
         // need aggressive condition, but not a good idea in general so use UG FIFO
         if ( requestData.notEmpty )
            begin
               requestData.deq ; // calls the last transaction complete
               idleSent <= False ;
               data <= getData( requestData.first ) ;
            end
         else
            begin
               idleSent <= True ;
            end
      endmethod

      method TransferType htrans() ;
         return requestData.notEmpty ? NONSEQ: IDLE ;
      endmethod
      method BusAddr haddr() ;
         return reqData.addr ;
      endmethod
      method RW hwrite() ;
         return reqData.read_write ;
      endmethod

      method BusData hwdata () ;
         return data ;
      endmethod 

      // XXX What about case when response FIFO is full -- we should not make request!
      // but the FIFO can be drained while waiting for the bus
      // Solution use a UG FIFO and overwrite when full !
      method Action hready( BusData hdata, BusStat hresp ) ;
         if ( ! idleSent )
            begin
               responseData.enq( BusResponse{ data:hdata, status:hresp} ) ;
            end
      endmethod
   endinterface
   
endmodule


// Add a register for request data.      
module mkBlueAmbaSlaveReg ( AmbaSlaveAdapter ) ;

   FIFOF#(AddrPhaseRequest) fRequest <- mkUGFIFOF ;
   RWire#(BusData)  rwData <- mkRWire ;
   RWire#(BusResponse) rwResponse <- mkRWire ;


   let  realresp = fromMaybe(errorResponse, rwResponse.wget ) ;
  
   interface BlueSlaveAdapter bbus ;
      method BusRequest request() if ( fRequest.notEmpty ) ;
         let areq = fRequest.first ;
         let data = fromMaybe( 0 , rwData.wget ) ;
         return BusRequest{ trans: areq.trans, addr: areq.addr, data:data, read_write: areq.read_write } ;
      endmethod

      method slaveSelect () ;
         return fRequest.notEmpty ;
      endmethod

      method Action response ( BusResponse resp ) if (fRequest.notEmpty) ;
         fRequest.deq() ;
         rwResponse.wset( resp ) ;
      endmethod

   endinterface

   interface Slave aslave ;
      // The high-level protocol assures that it can be written
      // Always allow a enq into this fifo 
      method Action hsel (BusAddr addr, RW rw, TransferType htrans );
         fRequest.enq ( AddrPhaseRequest{ trans: htrans, addr:addr, read_write:rw} )  ;
      endmethod

      method Action dataPhase( BusData bdata ) ;
         rwData.wset( bdata ) ;
      endmethod 

      method Bool hready () ;
         return isValid( rwResponse.wget ) ;
      endmethod
      method BusStat hresp() ;
         return realresp.status ;
      endmethod
      method BusData hrdata () ;
         return realresp.data ;
      endmethod

   endinterface

endmodule

   


import GetPut::* ;
import Connectable:: * ;


// Definitions for Address and Data Widths.
typedef Bit#(32) BusAddr ;
typedef Bit#(32) BusData ;

//  Enum fopr the bus transfer type
typedef enum { Write, Read } RW 
	deriving (Bits) ;

// structure to describe the bus request 
typedef struct {
                RW       read_write;
                BusData  data;
                BusAddr  addr;
                } BusRequest
deriving(Bits);

// Define a default request
BusRequest dummyRequest = BusRequest{ addr: 'hdead_add0 , data: 'hdead_da1a , read_write: Read } ;
BusRequest  idleRequest = BusRequest{ addr: 'hFFFF_FFFF , data: 'hFFFF_FFFF , read_write: Read } ;



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
BusResponse errorResponse = BusResponse{ data: 'hdead_badd, status: Error } ;
BusResponse defaultResponse = BusResponse{ data: 32'hdef0_def0, status: OK } ;


// ///////////////////////////////////////////////////////////////////////////
// The Master Interface
interface Master ;

   method ActionValue#(Bool) m_bus_request() ;
      // m_bus_request send a request to access to the bus

   method Action m_bus_grant( Bool bus_grant ) ;
      // m_bus_grant is an input received from the bus to show if the bus 
      // request has been granted.
      
   interface Get#(BusRequest) m_request;
      // The Get sub-interface provides the bus a way to get the request

   interface Put#(BusResponse) m_response;
      // The Put interface provides the bus a place to put the response.
endinterface


// The bus provides a BusMasterSide interface for each master it connects.
interface BusMasterSide ;
   method Action bms_bus_request ( Bool bus_request );
      // Takes a bus request input from the master

   method ActionValue#(Bool) bms_bus_grant ();
      // returns the bus grant to the master

   interface Put#(BusRequest) bms_request;
      // A sub-interface for the Master to place the request.

   interface Get#(BusResponse) bms_response ;
      // A sub-interface for the Master to set a response.
endinterface
   

// ///////////////////////////////////////////////////////////////////////////
// Slave and Bus Slave Side interfaces
// These are similar to the Master and MasterSide interface, except no bus request/grant
// are needed.
interface Slave ;
   interface Put#(BusRequest) s_request;
      // a place for the bus to put a request

   interface Get#(BusResponse) s_response;
      // a place for the bus to get a response
endinterface


interface BusSlaveSide ;
   interface Get#(BusRequest) bs_request ;
      // a place for the slave to get a request

   interface Put#(BusResponse) bs_response ;
      // a place the the slave to put a response
endinterface

// An example of an alternate Slave interface without using Get and Put sub-intrfaces
interface BusSlaveSide2 ;
   method ActionValue#(BusRequest) bs_request()  ;
   method Action                   bs_response( BusResponse response ) ;
endinterface




// ///////////////////////////////////////////////////////////////////////////
// Connectables describe the module needed to connect two interfaces
// 
instance Connectable#(Master, BusMasterSide) ;
      module mkConnection#(Master m, BusMasterSide b ) (Empty) ;
         // Connect the requests and the responses, using the mkConnection module 
         // defined for Get and Put interfaces
         mkConnection(m.m_request, b.bms_request) ;
         mkConnection(m.m_response, b.bms_response) ; 

         // a rule to transfer the request from the master to the bus
         (* no_implicit_conditions, fire_when_enabled *)
         rule connect_r  ;
            Bool m_request <- m.m_bus_request ;
            b.bms_bus_request( m_request ) ;
         endrule
         
         // A rule to transfer the grant from the bus to the master.
         (* no_implicit_conditions, fire_when_enabled *)
         rule connect_g ;
            Bool b_grant <- b.bms_bus_grant ;
            m.m_bus_grant( b_grant ) ;
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
         // Use the define connections for Get/Put
         mkConnection( s.s_request, b.bs_request ) ;
         mkConnection( s.s_response, b.bs_response ) ;
      endmodule
endinstance

// Provide another mkConnection for the Slave side with arguments reversed. 
instance Connectable#(BusSlaveSide, Slave) ;
      module mkConnection#(BusSlaveSide b, Slave s ) (Empty) ;
         mkConnection( s, b ) ;
      endmodule
endinstance



// ///////////////////////////////////////////////////////////////////////////      
interface B1m1s ;
   interface BusMasterSide ms0 ;
   interface BusSlaveSide ss0 ;
   interface BusSlaveSide defSlave ;
endinterface

      
interface B1m2s ;
   interface BusMasterSide ms0 ;
   interface BusSlaveSide ss0 ;
   interface BusSlaveSide ss1 ;
   interface BusSlaveSide defSlave ;
endinterface

         
interface B2m2s ;
   interface BusMasterSide ms0 ;
   interface BusMasterSide ms1 ;

   interface BusSlaveSide ss0 ;
   interface BusSlaveSide ss1 ;
      
   interface BusSlaveSide defSlave ;
endinterface

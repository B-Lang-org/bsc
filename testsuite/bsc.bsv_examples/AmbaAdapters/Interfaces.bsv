
import Connectable:: * ;
import Vector :: * ;

// Definitions for Address and Data Widths.
typedef Bit#(32) BusAddr ;
typedef Bit#(32) BusData ;

//  Enum for the bus transfer type
typedef enum { Write, Read } RW 
	deriving (Bits,Eq) ;

// structure to describe the bus request 
typedef struct {
                RW       read_write;
                BusData  data;
                BusAddr  addr;
                } BusRequest
deriving(Bits);

// Define a default request
BusRequest dummyRequest = BusRequest{ addr: 'hdead_add0 ,
                                      data: 'hdead_da1a ,
                                      read_write: Read } ;
BusAddr idleAddress = 'hFFFF_FFF0 ;
BusRequest  idleRequest = BusRequest{ addr: idleAddress ,
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
BusResponse errorResponse = BusResponse{ data: 'hdead_badd, 
                                         status: Error } ;
BusResponse defaultResponse = BusResponse{ data: 32'hdef0_def0, 
                                           status: OK } ;


// ///////////////////////////////////////////////////////////////////////////
// The Master Interface for Amba bus
interface Master ;

   method Bool busReq() ;
      // busReq sends a request to access to the bus

   method Action busGrant() ;
      // busGrant is an input received from the bus to show if the bus 
      // request has been granted.
      
   method ActionValue#(BusRequest) request();
      // request method provides the bus a way to get the request

   method Action response ( BusResponse resp ) ;
      // response provides the bus a place to put the response.
endinterface


// The bus provides a BusMasterSide interface for each master it connects.
interface BusMasterSide ;
   method Action bmsBusRequest ();
      // Takes a bus request input from the master

   method Bool bmsBusGrant ();
      // returns the bus grant to the master

   method Action bmsRequest ( BusRequest request ) ;
      // A method for the Master to place the request.

   method ActionValue#(BusResponse) bmsResponse ()  ;
      // A method for the Master to set a response.
endinterface




// For the slave side no change is needed??      
//      interface AmbaCSSlave ;
         
      
// ///////////////////////////////////////////////////////////////////////////
// Slave and Bus Slave Side interfaces
// These are similar to the Master and MasterSide interface, except no bus request/grant
// are needed.
interface Slave ;
   method Action request( BusRequest request ) ;
      // a place for the bus to put a request

   method  ActionValue#(BusResponse) response();
      // a place for the bus to get a response
endinterface


interface BusSlaveSide ;
   method ActionValue#(BusRequest) bsRequest ;
      // a place for the slave to get a request

   method Action bsResponse( BusResponse response ) ;
      // a place the the slave to put a response
endinterface

// An example of an alternate Slave interface without using Get and Put sub-intrfaces
interface BusSlaveSide2 ;
   method ActionValue#(BusRequest) bsRequest()  ;
   method Action                   bsResponse( BusResponse response ) ;
endinterface




// ///////////////////////////////////////////////////////////////////////////
// Connectables describe the module needed to connect two interfaces
// 
instance Connectable#(Master, BusMasterSide) ;
      module mkConnection#(Master m, BusMasterSide b ) (Empty) ;
         // a rule to transfer the request from the master to the bus
         (* no_implicit_conditions, fire_when_enabled *)
         rule connectMasterBusReq (m.busReq) ;
            b.bmsBusRequest() ;
         endrule
         
         // A rule to transfer the grant from the bus to the master.
         (* no_implicit_conditions, fire_when_enabled *)
         rule connectMasterBusGrant  ( b.bmsBusGrant );
            m.busGrant() ;
         endrule

         rule connectMasterRequest ;
            BusRequest r <- m.request ;
            b.bmsRequest( r ) ;
         endrule

         rule connectMasterResponse ;
            BusResponse r <- b.bmsResponse ;
            m.response( r ) ;
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
            BusRequest r <- b.bsRequest ;
            s.request( r ) ;
         endrule

         rule connectSlaveResponse ;
            BusResponse r <- s.response ;
            b.bsResponse( r ) ;
         endrule
         
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

interface B2m3s ;
   interface BusMasterSide ms0 ;
   interface BusMasterSide ms1 ;

   interface BusSlaveSide ss0 ;
   interface BusSlaveSide ss1 ;
   interface BusSlaveSide ss2 ;
      
   interface BusSlaveSide defSlave ;
endinterface

interface BusParam#(type mas, type slv ) ;
   interface Vector#(mas, BusMasterSide)  ms ;
   interface Vector#(slv, BusSlaveSide) ss ;

   interface BusSlaveSide defSlave ;
endinterface
      

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
      


      

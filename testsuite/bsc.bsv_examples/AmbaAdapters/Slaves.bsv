// Slave Modules for AMBA bus
import FIFO :: * ;
import FIFOF :: * ;
import RegFile :: * ;
import GetPut :: * ;
import Interfaces :: * ;
import AmbaAdapters :: * ;

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

   // only accpet request when counter is 1
   method Action request( BusRequest req ) if (counter == 1);
      // Set the counter and save the address.
      counter <= delayCntr ;
      oldAddr <= req.addr ;
   endmethod

   method ActionValue#(BusResponse) response () if ( counter == 1 );
      let resp = BusResponse{ data:oldAddr, status:OK } ;
      return resp;
   endmethod
   
endmodule


// //////////////////////////////////////////////////////////////////////////
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

   method Action request( BusRequest req );
      // Set the counter and save the address.
      counter <= truncate( req.data ) ;
      oldAddr <= req.addr ;
   endmethod

   method ActionValue#(BusResponse) response () if ( counter == 0 );
      let resp = BusResponse{ data:oldAddr, status:OK } ;
      return resp;
   endmethod
   
endmodule

// /////////////////////////////////////////////////////////////////////////
// A default slave which does nothing but always returns an OK status
(* synthesize *)
module defaultSlave( Slave ) ;

   // sub-interface for bus to place a request.
   method Action request( req ) ;
      // This method is always ready
      // $display( "default slave called:  %h, %h %h",
      //         req.read_write, req.addr, req.data ) ;
   endmethod

   method ActionValue#(BusResponse) response () ;
      return defaultResponse ;
   endmethod
endmodule




module mkADPSlave1( Slave ) ;

   AmbaSlaveAdapter adapter <- mkBlueAmbaSlave ;
   Slave slave_ifc = adapter.aslave ;
   BlueSlaveAdapter adapter_ifc = adapter.bbus ;

   // A fifo to hold the request
   FIFO#(BusRequest) requestQ <- mkFIFO ;

   rule takedata ( adapter_ifc.slaveSelect ) ;
      requestQ.enq( adapter_ifc.request ) ;
   endrule

   rule returndata ;
      // The implicit RDY condition is there must be something in requestQ
      let req = requestQ.first ;  requestQ.deq ;
      let addr = req.addr;
      // transfer address to data 
      let resp = BusResponse{ data:addr, status:OK } ;
      adapter_ifc.response( resp ) ;
   endrule 
   
   return slave_ifc ;
endmodule

module mkADPSlave#(Bit#(4) delayCntr ) ( Slave ) ;
   
   AmbaSlaveAdapter adapter <- mkBlueAmbaSlave ;
   Slave slave_ifc = adapter.aslave ;
   BlueSlaveAdapter adapter_ifc = adapter.bbus ;

   Reg#(Bit#(4)) counter <- mkReg( 0 ) ;
   Reg#(BusAddr) oldAddr <- mkReg( 0 ) ;
   // XXXX inProgress in not really needed since the respoinse can always be asserted?
   Reg#(Bool)   inProgress <- mkReg(False) ;
   
   rule takedata (( adapter_ifc.slaveSelect ) && (counter == 0))  ;
      oldAddr <=  adapter_ifc.request.addr ;
      counter <= delayCntr - 1;
      inProgress <= True ;
   endrule

     // Count down if the counter is not 0
   rule countDown ( counter != 0 ) ;
      counter <= counter - 1 ;
   endrule

   rule returndata ((counter == 0) && inProgress) ;
      // transfer address to data 
      let resp = BusResponse{ data:oldAddr, status:OK } ;
      adapter_ifc.response( resp ) ;
      inProgress <= False ;
   endrule 
   
   return slave_ifc ;
endmodule

(* synthesize *)
module mkSource ( Slave ) ;

   AmbaSlaveAdapter sadapter <- mkBlueAmbaSlaveReg ;
   BlueSlaveAdapter slave_adp = sadapter.bbus ;

   Reg#(BusData) cntr <- mkReg(0) ;
   Reg#(BusData) chksum <- mkReg(0) ;

   let validReadReq = (slave_adp.request.read_write == Read) && (slave_adp.request.addr[27:24] ==  0 ) ;
   rule validRead (slave_adp.slaveSelect && validReadReq ) ;
      slave_adp.response ( BusResponse { data: cntr , status: OK } ) ;
      chksum <= chksum+cntr;
      cntr <= cntr + 1 ;
      // $display( "mkSource %m: has sent: %0d chksum=%d", slave_adp.request.data, chksum ) ;
   endrule

   let checkSumReadReq = (slave_adp.request.addr[27:0]==28'h800_0000) && (slave_adp.request.read_write == Read)   ;
   rule readChksum (slave_adp.slaveSelect && checkSumReadReq ) ;
      slave_adp.response ( BusResponse { data: chksum , status: OK } ) ;
      // $display( "MKSOURCE %m: READING CHECKSUM: %0d chksum=%d", slave_adp.request.data, chksum ) ;
   endrule

   rule invalidOp ( slave_adp.slaveSelect && ! validReadReq && ! checkSumReadReq ) ;
      let req = slave_adp.request ;
      $display( "mkSource:: invalid  request %h %h %h",
               req.read_write, req.addr, req.data ) ;
      
      slave_adp.response ( errorResponse ) ;
   endrule

   return sadapter.aslave ;
endmodule

(* synthesize *)
module mkSink ( Slave ) ;

   AmbaSlaveAdapter sadapter <- mkBlueAmbaSlaveReg ;
   BlueSlaveAdapter slave_adp = sadapter.bbus ;

   Reg#(BusData) cntr <- mkReg(0) ;
   Reg#(BusData) chksum <- mkReg(0) ;

   let validWriteReq = (slave_adp.request.read_write == Write) && (slave_adp.request.addr[27:24] ==  0 ) ;
   rule validWrite (slave_adp.slaveSelect && validWriteReq ) ;
      slave_adp.response ( BusResponse { data:0  , status: OK } ) ;
      chksum <= chksum+slave_adp.request.data;
      // $display("mkSink %m:received: %0d chksum=%d", slave_adp.request.data, chksum ) ;
   endrule

   let readChksumReq = (slave_adp.request.addr[27:0]==28'h800_0000) && (slave_adp.request.read_write == Read  ) ;
   rule readChksum (slave_adp.slaveSelect && readChksumReq ) ;
      slave_adp.response ( BusResponse { data: chksum , status: OK } ) ;
      // $display("MKSINK %m: READING CHECKSUM: %0d chksum=%d", slave_adp.request.data, chksum ) ;
   endrule

   rule invalidOp ( slave_adp.slaveSelect && ! validWriteReq && ! readChksumReq ) ;
      let req = slave_adp.request ;
      $display( "mkSink:: invalid  request %h %h %h",
               req.read_write, req.addr, req.data ) ;
      
      slave_adp.response ( errorResponse ) ;
   endrule
   
   return sadapter.aslave ;
endmodule

typedef Bit#(32) RxData ;

interface Rx ;
   method Action rx( RxData rxdata);
endinterface

interface SlaveRx ;
   interface Slave slave ;
   method Action rx( RxData rxdata);
//   interface Rx    rx;
endinterface


(* synthesize *)



module mkSlaveRx ( SlaveRx ) ;

   AmbaSlaveAdapter sadapter <- mkBlueAmbaSlaveReg ;
   BlueSlaveAdapter slave_adp = sadapter.bbus ;

   Reg#(BusData) cntr <- mkReg(0) ;
   Reg#(BusData) chksum <- mkReg(0) ;

   rule readData (slave_adp.slaveSelect && slave_adp.request.addr[27]==0 && slave_adp.request.read_write == Read) ;
      slave_adp.response ( BusResponse { data: cntr , status: OK } ) ;
      chksum <= chksum+cntr;
      cntr <= cntr + 1 ;
      // $display( "mkSource %m: has sent: %0d chksum=%d", slave_adp.request.data, chksum ) ;
   endrule

   rule readChksum (slave_adp.slaveSelect && slave_adp.request.addr[27:0]==28'h800_0000 && slave_adp.request.read_write == Read  ) ;
      slave_adp.response ( BusResponse { data: chksum , status: OK } ) ;
      // $display( "MKSOURCE %m: READING CHECKSUM: %0d chksum=%d", slave_adp.request.data, chksum ) ;
   endrule


   method Action rx( RxData rxdata);
      // $display("In rx: rxdata = %d",rxdata);
   endmethod
   
   interface slave = sadapter.aslave;
endmodule


typedef Bit#(32) TxData ;

interface Tx ;
   // method TxData tx;
   method ActionValue#(TxData) tx ()  ;

endinterface

interface SlaveTx ;
   interface Slave slave ;
   method ActionValue#(TxData) tx ()  ;
//   interface Tx    tx;
endinterface



(* synthesize *)
module mkSlaveTx ( SlaveTx ) ;

   AmbaSlaveAdapter sadapter <- mkBlueAmbaSlaveReg ;
   BlueSlaveAdapter slave_adp = sadapter.bbus ;

   Reg#(BusData) cntr <- mkReg(0) ;
   Reg#(BusData) chksum <- mkReg(0) ;

   // A fifo to buffer TX Data
   FIFOF#(TxData) txfifo <- mkUGFIFOF;  // BOZO FIXME - guarded version hangs???

   Bool writedata = (slave_adp.slaveSelect && slave_adp.request.addr[27]==0 && slave_adp.request.read_write==Write) ;

   rule writeData (slave_adp.slaveSelect && slave_adp.request.addr[27]==0 && slave_adp.request.read_write==Write) ;
      slave_adp.response ( BusResponse { data:0  , status: OK } ) ;
      // txfifo.enq(slave_adp.request.data); // BOZO FIXME - will uncomment later
      chksum <= chksum+slave_adp.request.data;
      // $display("mkSink %m:received: %0d chksum=%d", slave_adp.request.data, chksum ) ;
   endrule
   
   rule readChksum (slave_adp.slaveSelect && slave_adp.request.addr[27:0]==28'h800_0000 && slave_adp.request.read_write == Read  ) ;
      slave_adp.response ( BusResponse { data: chksum , status: OK } ) ;
      // $display("MKSINK %m: READING CHECKSUM: %0d chksum=%d", slave_adp.request.data, chksum ) ;
   endrule
   
   method ActionValue#(TxData) tx ()  ;
      txfifo.deq;
      return txfifo.first; 
   endmethod
   
   interface slave = sadapter.aslave;
endmodule



module mkSRAM64k ( Slave ) ;

   RegFile#(Bit#(16), BusData ) rfile <- mkRegFileFull ;

   AmbaSlaveAdapter sadapter <- mkBlueAmbaSlaveReg ;
   BlueSlaveAdapter slave_adp = sadapter.bbus ;

   rule writeMem ( slave_adp.slaveSelect &&
                  slave_adp.request.read_write == Write) ;
      let addr = slave_adp.request.addr[17:2] ;
      let datw = slave_adp.request.data ;
      rfile.upd( addr, datw ) ;
      slave_adp.response ( BusResponse { data: 0 , status: OK } ) ;      
   endrule

   rule readMem ( slave_adp.slaveSelect &&
                  slave_adp.request.read_write == Read ) ;
      let addr = slave_adp.request.addr[17:2] ;
      let datr = rfile.sub( addr ) ;
      slave_adp.response ( BusResponse { data: datr , status: OK } ) ;      
   endrule

   return sadapter.aslave;
   
endmodule



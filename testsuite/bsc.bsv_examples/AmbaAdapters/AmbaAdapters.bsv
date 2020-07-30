import Interfaces :: * ;
import FIFOF :: * ;
import ConfigReg :: * ;

module mkBlueAmbaMaster ( AmbaMasterAdapter ) ;

   FIFOF#(BusRequest) requestData <- mkUGFIFOF ;
   FIFOF#(BusResponse) responseData <- mkUGFIFOF ;
   RWire#(Bool) r_granted <- mkRWire ;
   Reg#(Bool) idleSent <- mkConfigReg( True ) ;
   
   interface BlueMasterAdapter bbus ;
      method Action read( address ) if ( requestData.notFull )  ;
         requestData.enq( BusRequest{ addr:address, data:0, read_write: Read } ) ;
      endmethod
      
      method Action write( address, wdata ) if ( requestData.notFull )  ;
         requestData.enq( BusRequest{ addr:address, data:wdata, read_write: Write } ) ;
      endmethod
   
      method BusResponse response () if ( responseData.notEmpty ) ;
         return responseData.first ;
      endmethod

      method Action takeResponse () if (responseData.notEmpty ) ;
         responseData.deq ;
      endmethod
   endinterface

   interface Master amaster ;
      // method is always enabled XXX can  to Bit#(0)
      method Bool busReq();
         return  requestData.notEmpty ;
      endmethod

      // XXX argument is not needed  EN is sufficient
      method Action busGrant () ;
         r_granted.wset(True) ;
      endmethod

      method ActionValue#(BusRequest) request () if (r_granted.wget matches tagged Valid True ) ;
         // 2 cases here, since a bus can be granted even when not request
         // need aggressive condition, but not a good idea in general so use UG FIFO
         let reqData = dummyRequest ;
         if ( requestData.notEmpty )
            begin
               reqData = requestData.first ;
               requestData.deq ; // calls the last transaction complete
               idleSent <= False ;
            end
         else
            begin
               idleSent <= True ;
               reqData = idleRequest ;
            end
         return reqData ;
      endmethod

      // XXX What about case when response FIFO is full -- we should not make request!
      // but the FIFO can be drained while waiting for the bus
      // Solution use a UG FIFO and overwrite when full !
      method Action response( BusResponse resp ) ;
         if ( ! idleSent )
            begin
               responseData.enq( resp ) ;
            end
      endmethod
   endinterface
   
endmodule

module mkBlueAmbaSlave ( AmbaSlaveAdapter ) ;

   RWire#(BusRequest) rwRequest <- mkRWire ;
   RWire#(BusResponse) rwResponse <- mkRWire ;

   interface BlueSlaveAdapter bbus ;
      method request() ;
         return fromMaybe( dummyRequest, rwRequest.wget ) ;
      endmethod

      method slaveSelect () ;
         return isValid( rwRequest.wget) ;
      endmethod

      method Action response ( BusResponse resp ) ;
         rwResponse.wset( resp ) ;
      endmethod

   endinterface

   interface Slave aslave ;
      // The high-level protocol assures that it can be written
      method Action request (BusRequest req);
         rwRequest.wset( req ) ;
      endmethod
      
      method ActionValue#(BusResponse) response() if ( isValid( rwResponse.wget ) );
         return validValue( rwResponse.wget ) ;
      endmethod
   endinterface

endmodule

   

// Add a register for request data.      
module mkBlueAmbaSlaveReg ( AmbaSlaveAdapter ) ;

   FIFOF#(BusRequest) fRequest <- mkFIFOF ;
   RWire#(BusResponse) rwResponse <- mkRWire ;

   interface BlueSlaveAdapter bbus ;
      method request() ;
         return fRequest.first ;
      endmethod

      method slaveSelect () ;
         return fRequest.notEmpty ;
      endmethod

      method Action response ( BusResponse resp ) ;
         fRequest.deq() ;
         rwResponse.wset( resp ) ;
      endmethod

   endinterface

   interface Slave aslave ;
      // The high-level protocol assures that it can be written
      method Action request (BusRequest req);
         fRequest.enq ( req )  ;
      endmethod
      
      method ActionValue#(BusResponse) response() if ( isValid( rwResponse.wget ) );
         return validValue( rwResponse.wget ) ;
      endmethod
   endinterface

endmodule

   

      


import Interfaces :: * ;
import FIFO :: * ;
import FIFOF :: * ;
import GetPut :: * ;
import LFSR :: * ;
import ConfigReg :: * ;
import RegFile :: * ;

// a function to add a time stamp/counter to the transaction address.
function BusAddr modAddress( BusRequest reqin, Bit#(28) cntr );
   let newAddr = { reqin.addr[31:28], cntr} ;
   return newAddr ;
endfunction

// a parameterized master.
// Note that this cannot be synthezied to Verilog, only via a top level wrapper
module mkMasterP#(Bit#(28) report, Bit#(16) seed, Bit#(8) cutoff, String id)  ( Master );

   // A counter to show that we are alive and to generate addresses
   Reg#(Bit#(28)) counter <-  mkConfigReg(0) ;
   Reg#(Bit#(32)) blockedCount <- mkConfigReg(0) ;
   Reg#(Bit#(32)) reqCount <- mkConfigReg(0) ;
   Reg#(Bit#(32)) passCount <- mkConfigReg(0) ;

   // TODO make this an array of registers
   Reg#(Bit#(32)) delay0 <- mkReg(0) ;
   Reg#(Bit#(32)) delay1 <- mkReg(0) ;
   Reg#(Bit#(32)) delay2 <- mkReg(0) ;
   Reg#(Bit#(32)) delay3 <- mkReg(0) ;
   Reg#(Bit#(32)) delay4 <- mkReg(0) ;
   Reg#(Bit#(32)) delay5 <- mkReg(0) ;
   Reg#(Bit#(32)) delay6 <- mkReg(0) ;
   Reg#(Bit#(32)) delayn <- mkReg(0) ;

   Reg#(Bit#(32)) weightedDelayR <- mkReg(0) ;
   
   // An LFSR for random addresses
   //   LFSR #(Bit#(16)) random <- mkRCounter( 0 ) ; // for debug
   LFSR #(Bit#(16)) random <-  mkLFSR_16 ; // for pseudo random numbers
   
   // a register for the request data, use unguarded fifo to allow idle requests!
   FIFOF#(BusRequest) requestData <- mkUGFIFOF1 ;

   // A fifo to track the request times
   FIFOF#(Bit#(28)) reqTrackFifo <- mkUGFIFOF ;

   // A fifo to hold delay times for later processing processing 
   FIFO#(Bit#(4)) delayF <- mkFIFO ;
   
      // Rule to start the simulation and turn on vcd dumps
   rule init ( counter == 0 ) ;
      //$dumpvars() ;
      //$dumpon() ;
      random.seed( seed ) ;
      counter <= 1 ;
   endrule

   rule dlay0 ( delayF.first == 0 ) ;
      delayF.deq ;
      delay0 <= delay0 + 1 ;
      $display( "Zero delay !! " ) ;
   endrule
   rule dlay1 ( delayF.first == 1 ) ;
      delayF.deq ;
      delay1 <= delay1 + 1 ;
   endrule
   rule dlay2 ( delayF.first == 2 ) ;
      delayF.deq ;
      delay2 <= delay2 + 1 ;
   endrule
   rule dlay3 ( delayF.first == 3 ) ;
      delayF.deq ;
      delay3 <= delay3 + 1 ;
   endrule
   rule dlay4 ( delayF.first == 4 ) ;
      delayF.deq ;
      delay4 <= delay4 + 1 ;
   endrule
   rule dlay5 ( delayF.first == 5 ) ;
      delayF.deq ;
      delay5 <= delay5 + 1 ;
   endrule
   rule dlay6 ( delayF.first == 6 ) ;
      delayF.deq ;
      delay6 <= delay6 + 1 ;
   endrule
   rule dlayn ( delayF.first > 6 ) ;
      delayF.deq ;
      delayn <= delayn + 1 ;
   endrule
   
        
   // rule to count, report data and end the simulations
   rule count ( counter > 0 ) ;
      counter <= counter + 1;
   endrule

   rule rtp1 ( counter ==  report) ;
      $display( "%s Cycle count: %0d", id, counter ) ;
      $display( "%s Blocked count: %0d", id, blockedCount ) ;
      $display( "%s Req count: %0d", id, reqCount ) ;
      $display( "%s Pass count: %0d", id, passCount ) ;

      $display( "%s Delay count %0d = %0d", id, 0, delay0 ) ;
      $display( "%s Delay count %0d = %0d", id, 1, delay1 ) ;
      $display( "%s Delay count %0d = %0d", id, 2, delay2 ) ;
      $display( "%s Delay count %0d = %0d", id, 3, delay3 ) ;
      $display( "%s Delay count %0d = %0d", id, 4, delay4 ) ;
      $display( "%s Delay count %0d = %0d", id, 5, delay5 ) ;
      $display( "%s Delay count %0d = %0d", id, 6, delay6 ) ;
      $display( "%s Delay count %0d = %0d", id, 7, delayn ) ;
      $display( "%s Average Delay = %0d / %0d", id, weightedDelayR, reqCount ) ;

   endrule

   // delay the finish to allow other modules to report.
   rule fin ( counter == report + 1 ) ;
      $finish(0) ;
   endrule
   
   // rule to generate new request data
   rule newdata ((truncate(random.value) < cutoff ) && (requestData.notFull)) ;
      random.next;
      reqCount <= reqCount + 1;
      reqTrackFifo.enq( counter ) ;
     
      Bit#(4) high = truncate( random.value ) ;       // grab a 4 bit random number
      let reqaddr = {high, counter };
      requestData.enq( BusRequest {addr:reqaddr, data:1, read_write:Read } ) ;

   endrule

   // Count number of time the 
   rule blocked ((truncate(random.value) < cutoff ) && (! requestData.notFull));
      blockedCount <= blockedCount + 1 ;
      // $display( "%s blocked at %0d", id, counter ) ;
   endrule
   
   // advance random number if no request.
   rule noRequest (truncate(random.value) >= cutoff ) ;
      random.next ;
      passCount <= passCount + 1 ;
   endrule
   
   // Let the master know that a grant was received
   RWire#(Bool)  r_granted <- mkRWire ;

   // Keeps track if the master has send an idle transaction.
   Reg#(Bool) idleSent <- mkReg( True );


   // methods and interface definitions ////////////////////////////////////////
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
               // if ( ! reqTrackFifo.notEmpty ) $display( "Unexpected !!!" ) ;
               
               // $display( "response %s: counter: %0d  stat: %h, data: %h", id,
               // counter, response.status, response.data ) ;

               let enqCnt = reqTrackFifo.first ; reqTrackFifo.deq ;
               let diff = counter - enqCnt ;
               weightedDelayR <= weightedDelayR + zeroExtend( diff ) ;
               delayF.enq( (diff < 15) ? truncate( diff ) : 15  ) ;
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
               // $display( "sending request %s -- %0d %h %h %b", id,
               // counter, reqData.addr, reqData.data, reqData.read_write) ;

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
// (* synthesize *)
// module mkMaster_500_1 (Master ) ;
//    Master localM <- mkMasterP(500,1, 64, "A" ) ;
//    return localM ;
// endmodule

// (* synthesize *)
// module mkMaster_500_6 (Master ) ;
//    Master localM <- mkMasterP(500,6,64, "B") ;
//    return localM ;
// endmodule

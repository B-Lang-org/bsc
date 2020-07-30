

import Clocks :: * ; 


interface Top ;
   method Action    bytein( Bit#(8)  din ) ;
   method Action    wordin( Bit#(32)  word_in ) ;
   method Bit#(32)  dataOut () ;
endinterface


interface ByteReader ;
   method Action     byte_in( Bit#(8)  data ) ;
   method Bit#(32)   wordOut ()  ;
   method Bool       pulseOut() ;
endinterface

interface WordCruncher ;
   method Action   crunch( Bit#(32) dataRead, Bit#(32) codein ) ;
   method Bit#(32) dataOut () ;
endinterface
   

(* synthesize *)
// default clock in the clock for the data cruncher       
module mkTopLevel( Clock readClk, Reset readRst,
                  Top ifc );

   ByteReader reader_ifc() ;
   mkByteReader  reader( reader_ifc, clocked_by( readClk ), reset_by( readRst ) ) ;

   WordCruncher wrd_crunch_ifc() ;
   mkWordCrunch wrd_crunch( wrd_crunch_ifc ) ;


   //Use a fifo synchronizer
   SyncFIFOIfc#(Bit#(32))  sync_ifc() ;
   mkSyncFIFOToCC syncer( 4, readClk, readRst, sync_ifc ) ;
   
   rule loadSync( reader_ifc.pulseOut ) ;
      sync_ifc.enq( reader_ifc.wordOut ) ;
   endrule
   
   method Action    bytein( Bit#(8)  din ) ;
      reader_ifc.byte_in( din ) ;
   endmethod
   
   method Action    wordin( Bit#(32)  word_in ) ;
      wrd_crunch_ifc.crunch(sync_ifc.first, word_in );
      sync_ifc.deq ;
   endmethod

   method Bit#(32)  dataOut () ;
      return wrd_crunch_ifc.dataOut ;
   endmethod
   
   
endmodule


module mkByteReader(  ByteReader ) ;

   Reg#(Bit#(2))  cntr <- mkReg( 0 ) ;
   
   Reg#(Bit#(8))  r0 <- mkReg( 0 );
   Reg#(Bit#(8))  r1 <- mkReg( 0 );
   Reg#(Bit#(8))  r2 <- mkReg( 0 );

   Reg#(Bit#(32))  result <- mkReg( 0 ) ;

   Reg#(Bool) pulse <- mkReg( False );

   rule clrPulse( pulse ) ;
      pulse <= False ;
   endrule
   
   method Action byte_in( data );
      case ( cntr )
         2'b00: begin
                   r0 <= data ;
                end
         2'b01: begin
                   r1 <= data ;
                   end
         2'b10: begin
                   r2 <= data ;
                end
         2'b11: begin
                   result <= { data, r2, r1, r0 } ;
                   pulse <= True ;
                end
      endcase
      cntr <= cntr + 1 ;        
   endmethod

   method wordOut ;
      return result ;
   endmethod

   method pulseOut ;
      return pulse;
   endmethod
endmodule

module mkWordCrunch( WordCruncher ) ;

   Reg#(Bit#(32))  result <- mkReg( 0 );
   
   method Action   crunch( Bit#(32) dataRead, Bit#(32) codein ) ;
      result <= dataRead ^ codein ;
   endmethod
   
   method Bit#(32) dataOut () ;
      return result ;
   endmethod
endmodule

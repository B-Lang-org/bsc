
import FIFO :: * ;
import Vector :: * ;



typedef 6 Size ;
typedef Bit#(10) Idx ;
typedef UInt#(6) Cntr ;

interface Test1 ;
   method Action setGo  (Idx index) ;
   method Action clearGo(Idx index) ;
   method Action deq () ;
   method Cntr first ;
endinterface

(* synthesize *)
module sysDUFunction1( Test1 ) ;

   // A Vector of Reg of Bools
   Vector#(Size,Reg#(Bool))  gos <- replicateM( mkReg(False) ) ;

   // A Vector of Reg of States
   Vector#(Size,Reg#(Cntr)) cntrs <- replicateM( mkReg(0) ) ;

   // A common resource for which the rules compete.
   FIFO#(Cntr) outf <- mkSizedFIFO( 8 ) ;
   FIFO#(Cntr) outf2 <- mkSizedFIFO( 8 ) ;

   function Rules buildRules( Integer i ) ;
      begin return 
         rules
            rule doit ( gos[i]._read ) ;
               cntrs[i]._write ( cntrs[i]._read + 1 ) ;
               outf.enq(  cntrs[i]._read ) ;
            endrule
         endrules ;
      end
   endfunction


   Vector#(Size,Rules) genrules = map( buildRules, genVector ) ;

   //mapM_( addRules, genrules ) ;
   // Generates conflicts as expected.

   // Objective 
   let rx = foldl1( rJoinDescendingUrgency, genrules) ;
   addRules( rx ) ;
   
   method Action setGo( Idx index ) ;
      let breg = select( gos, index ) ;
      breg <= True ;
   endmethod

   method Action clearGo( Idx index ) ;
//      let breg = select( gos, index ) ;
//      breg <= False ;
   endmethod

   method Action deq = outf.deq ;
   method first = outf.first ;
      
endmodule

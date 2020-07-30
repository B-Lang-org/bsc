
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
module sysDUFunction5( Test1 ) ;

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

   let foo = rules
                (* descending_urgency = "x2, x1" *)
                rule x1 ( gos[1]._read ) ;
                   outf2.deq;
                endrule
                rule x2 ( gos[2]._read ) ;
                   outf2.deq;
                endrule
                // The rule below can nver fire.   It should be renames
                rule x3 ( gos[2]._read ) ;
                   outf2.deq;
                endrule
             endrules;

   // test that the urgency annotation can be here, even before x4 is defined.
   (* descending_urgency = "x3, x4, x1, doit, doit_3, doit_2, doit_4, doit_5" *)
   rule x3 ( gos[0]._read ) ;
      outf2.deq;
   endrule
   rule x4 ( gos[3]._read ) ;
      outf2.deq;
   endrule
   
   Vector#(Size,Rules) genrules = map( buildRules, genVector ) ;

   //mapM_( addRules, genrules ) ;
   // Generates conflicts as expected.

   // Objective 
   let rx = foldl1( rJoin, genrules) ;
   let ry = rJoinPreempts( foo, rx ) ;
   addRules( ry ) ;
//   addRules( rx ) ;
//   addRules( foo ) ;
   
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

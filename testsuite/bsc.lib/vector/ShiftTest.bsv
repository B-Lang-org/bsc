
import Vector :: * ;
import StmtFSM :: * ;


typedef  Bit#(4) Basic ;
typedef Vector#(6,Basic)  BasicV ;

(* synthesize *)
module sysShiftTest() ;

   Reg#(BasicV) current <- mkReg( map( fromInteger, genVector ) ) ;
   Reg#(UInt#(3)) idx <- mkReg( 1 ) ;


   function Action displayVs( String s ) ;
      return
      action
         $display( "%s", s ) ;
         $display( "Values are [5:0]:    %h, %h, %h, %h, %h, %h",
                  current[5], current[4],
                  current[3], current[2],
                  current[1], current[0] ) ;
         $display( "Packed values are: %h", pack( current ) ) ;
      endaction;
   endfunction

   Vector#(16,Basic) foo =  map( fromInteger, genVector ) ;
   
   Stmt testseq =
   seq

      displayVs( "initial" ) ;
      current <= shiftInAt0( current, 9 ) ;
      displayVs( "shift 9 in at 0" ) ;
      current <= shiftInAt0( current, 10 ) ;
      displayVs( "shift 10 in at 0 " ) ;
      current <= shiftInAt0( current, 1 ) ;
      displayVs( "shift 1 in at 0" ) ;

      current <= shiftInAtN( current, 1 ) ;
      displayVs( "shift 1 in at N" ) ;

      current <= shiftInAtN( current, 6 ) ;
      displayVs( "shift 6 in at N" ) ;

      current <= shiftInAtN( current, 15 ) ;
      
      displayVs( "shift f in at N" ) ;

      $display ("foo of 0 is %h",  foo[0] ) ;
      current <= take( foo ) ;
      displayVs( "take from 16" ) ;

      current <= takeTail( foo ) ;
      displayVs( "take Take from 16" ) ;

      current <= takeAt( 1, foo ) ;
      displayVs( "take from 16 at 1" ) ;

      current <= takeAt( 7, foo ) ;
      displayVs( "take from 16 at 7" ) ;
      current <= takeAt( 10, foo ) ;
      displayVs( "take from 16 at 7" ) ;

      // following should give compile error
      //current <= takeAt( 10, foo ) ;

      // Try some dynamic indexing
      action
         $display( "Index %d of foo is %h", idx, current[idx] ) ;
         idx <= idx + 2 ;
      endaction
      action
         $display( "Index %d of foo is %h", idx, current[idx] ) ;
         idx <= idx + 2 ;
      endaction
      action
         $display( "Index %d of foo is %h", idx, current[idx] ) ;
         idx <= idx + 2 ;
      endaction
      action
         $display( "Index %d of foo is %h", idx, current[idx] ) ;
         idx <= idx + 2 ;
      endaction
      action
         $display( "Index %d of foo is %h", idx, current[idx] ) ;
         idx <= idx + 2 ;
      endaction

//      current[idx] <= 4 ;
//      displayVs( "idx updated to to 4") ;
   endseq;

   mkAutoFSM( testseq ) ;
   
   
endmodule

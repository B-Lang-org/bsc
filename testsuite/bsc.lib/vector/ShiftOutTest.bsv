
import Vector :: * ;
import StmtFSM :: * ;


typedef  Bit#(4) Basic ;
typedef Vector#(6,Basic)  BasicV ;

(* synthesize *)
module sysShiftOutTest() ;

   Reg#(BasicV) current <- mkReg( map( fromInteger, genVector ) ) ;
   Reg#(UInt#(3)) idx <- mkReg( 1 ) ;
   Reg#(UInt#(4)) idx2 <- mkReg( 1 ) ;
   Reg#(Bit#(2)) idx3 <- mkReg( 1 ) ;
   Reg#(BasicV) readonly <- mkReg(map( fromInteger, genVector ) ) ;

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

   function Action displayVs2( String s, Vector#(6,Basic) c ) ;
      return
      action
         $display( "%s", s ) ;
         $display( "Values are [5:0]:    %h, %h, %h, %h, %h, %h",
                  c[5], c[4],
                  c[3], c[2],
                  c[1], c[0] ) ;
         $display( "Packed values are: %h", pack( c ) ) ;
      endaction;
   endfunction

   Vector#(16,Basic) foo =  map( fromInteger, genVector ) ;
   Vector#(13,Basic) oddv =  map( fromInteger, genVector ) ;
   BasicV bv =  readonly._read;

   Stmt testseq =
   seq

      displayVs( "initial" ) ;
      current <= shiftOutFrom0( 0, current, 0 ) ;
      displayVs( "shift 0 out from 0" ) ;

      current <= bv ;
      current <= shiftOutFrom0( 0, current, 3 ) ;
      displayVs( "shift 3 out from 0" ) ;

      current <= bv ;
      current <= shiftOutFrom0( 0, current, 9 ) ;
      displayVs( "shift 9 out from 0 " ) ;

      current <= bv ;
      current <= shiftOutFrom0( 0, current, 1 ) ;
      displayVs( "shift 1 out from 0" ) ;

      /////////////////////////////////
      $display ( "-------------------------------------------" );
      current <= bv ;
      current <= shiftOutFromN( 0, current, 0 ) ;
      displayVs( "shift 0 out from N" ) ;

      current <= bv ;
      current <= shiftOutFromN( 0, current, 3 ) ;
      displayVs( "shift 1 out from N" ) ;
      
      current <= bv ;
      current <= shiftOutFromN( 0, current, 9 ) ;
      displayVs( "shift 9 out from N" ) ;

      current <= bv ;
      current <= shiftOutFromN( 0, current, 1 ) ;
      displayVs( "shift 1 out from N" ) ;


      // Dynamic shifts
      idx2 <= 0;
      while (idx2 != maxBound ) seq
         action
            let tmp0 = shiftOutFrom0 ( maxBound, bv, idx2 );
            let tmpN = shiftOutFromN ( maxBound, bv, idx2 );
            $display ("-------------------------------------------------- Shift amount = %d", idx2);
            displayVs2 ( "out 0:", tmp0 );
            displayVs2 ( "out N:", tmpN );
            idx2 <= idx2 + 1 ;
         endaction
      endseq
      
      idx3 <= 0;
      while (idx3 != maxBound ) seq
         action
            let tmp0 = shiftOutFrom0 ( maxBound, bv, {1'b0,idx3} );
            let tmpN = shiftOutFromN ( maxBound, bv, {1'b0,idx3} );
            $display ("-------------------------------------------------- Shift amount = %d", idx3);
            displayVs2 ( "out 0:", tmp0 );
            displayVs2 ( "out N:", tmpN );
            idx3 <= idx3 + 1 ;
         endaction
      endseq
      
   endseq;
   

   mkAutoFSM( testseq ) ;
   
   
endmodule

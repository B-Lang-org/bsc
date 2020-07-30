// Tests for 
import Vector :: * ;
import StmtFSM :: * ;


typedef  Bit#(4) Basic ;
typedef Vector#(6,Basic)  BasicV ;

(* synthesize *)
module sysMiscFunc() ;

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
   
   Vector#(6, Reg#(Basic)) vregs <- replicateM (mkReg(0));

   Reg#(Bit#(7))  xx1 <- mkReg(0);
   Reg#(Bit#(8))  xx8 <- mkReg(0);

   function Action dv (xxx) = $display ( "%b msb = %b parity = %b, rev = %b, Ones = %d, MSB zeros = %d, LSB zeros = %d", 
                                        xxx, msb(xxx), parity(xxx), reverseBits(xxx), 
                                        countOnes(xxx), countZerosMSB(xxx), countZerosLSB(xxx) );


   function Action ds( x, y) = $display( "%b,  truncateLSB = %b ", x, y ) ;
   function Action rtrun ( f ) = 
      action
         Bit#(6) f6 = truncateLSB(f);
         ds( f, f6 );
         Bit#(5) f5 = truncateLSB(f);
         ds( f, f5 );
         Bit#(4) f4 = truncateLSB(f);
         ds( f, f4 );
         Bit#(3) f3 = truncateLSB(f);
         ds( f, f3 );
         Bit#(2) f2 = truncateLSB(f);
         ds( f, f2 );
         Bit#(1) f1 = truncateLSB(f);
         ds( f, f1 );
         Bit#(0) f0 = truncateLSB(f);
         ds( f, f0 );           
      endaction ;
      
   
   Stmt testseq =
   seq

      displayVs( "initial" ) ;
      writeVReg( vregs, drop (foo) );
      current <= readVReg (vregs);
      displayVs( "read & writeVreg" ) ;
      writeVReg( vregs, take (foo) );
      current <= readVReg (vregs);
      displayVs( "read & writeVreg head" ) ;
      $display ( "reverseBits: %b %b", pack(current), reverseBits(pack(current)) ) ;
      
      action
         xx1 <= 1 ;
      endaction
      action 
         dv(xx1);
         xx1 <= 3 ;
      endaction
      action 
         dv(xx1) ;
         xx1 <= 2 ;
      endaction
      action 
         dv(xx1) ;
         xx1 <= 7'h41 ;
      endaction
      action 
         dv(xx1) ;
         xx1 <= 7'h42 ;
      endaction
      action 
         dv(xx1) ;
         xx1 <= 7'h43 ; 
      endaction
      action 
         dv(xx1) ;
         xx1 <= 7'h43 ; 
      endaction
      action 
         dv(xx1) ;
         xx1 <= 7'h50 ; 
      endaction
      action 
         dv(xx1) ;
         xx1 <= 7'h05 ; 
      endaction
      action  
         dv(xx1);

         xx8 <= '1 ; 
      endaction
      action 
         dv(xx8);
         xx8 <= '0 ;
      endaction
      action  
         dv(xx8);
         xx8 <= 'haa ;
      endaction
      action 
         dv(xx8);
         xx8 <= 'h55 ;
      endaction
      action 
         dv(xx8);
         xx8 <= 'h81 ;
      endaction
      action 
         dv(xx8);
      endaction
      action
         rtrun(xx8) ;
         xx8 <= 'hbc ;
         Bit#(7) f = 7'b0010011 ;
         rtrun(f) ;
         rtrun( reverseBits(f)) ; 
         rtrun ( 9'b1100_01111 );
      endaction
      action
         rtrun(xx8);
      endaction
  endseq;

   mkAutoFSM( testseq ) ;
   
   
endmodule


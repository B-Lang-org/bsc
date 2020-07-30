import Vector :: * ;


typedef struct {
                Int#(8) i;
                Bool valid ;
                }  BE
deriving (Bits, Eq ) ;

BE xNull = BE { i:-1, valid: False } ;
BE x0 = BE { i:0, valid: True } ;
BE x1 = BE { i:1, valid: True } ;
BE x2 = BE { i:2, valid: False } ;
BE x3 = BE { i:3, valid: True } ;
BE x4 = BE { i:4, valid: False } ;
BE x5 = BE { i:5, valid: True } ;
BE x6 = BE { i:6, valid: True } ;
BE x7 = BE { i:7, valid: True } ;

function Bool beIsValid ( BE din ) ;
   return din.valid;
endfunction


function Bool beIsGreaterThan ( Int#(8) test , BE din ) ;
   return din.valid && (din.i > test) ;
endfunction

function Action printBE ( BE v ) ;
   return
   action
      $write("{%h,%b} ", v.i, v.valid  ) ;
   endaction;
endfunction

function Action printv ( Vector#(n,BE) v ) ;
   return
   action
   Integer i = 0 ;
   for ( i = 0 ; i < valueof(n); i = i + 1 ) 
      begin
         $write( "V[%0d]=", i ) ;
         printBE( v[i] ) ;
      end
   $display();
   endaction ;
endfunction


(* synthesize *) 
module sysRotateBy ();
   // +rotateBy :: (Log n lgn, Add xxx 1 (TExp n) ) => Vector n a -> UInt lgn ->  Vector n a 
   // +rotateBy vin amt =
   
   Reg#(int) cnt <- mkReg(0) ;
   Reg#(UInt#(3)) shiftAmt <- mkReg(0) ;
   
   Reg#( Vector#(8,BE) )  t1 <- mkReg( replicate(x0) ) ;
   
   rule c ;
      cnt <= cnt + 1 ;
      if( cnt > 100 ) $finish(0) ;
   endrule
   
   rule x0 ( cnt == 0 || cnt == 10 ) ;
      printv ( t1 ) ;
      let t = t1 ;
      t[1] = x1 ;
      t[2] = x2 ;
      t[3] = x3 ;
      t[4] = x4 ;
      t[5] = x5 ;
      t[6] = x6 ;
      t[7] = x7 ;
      
      t1 <= t ;
   endrule

      
   rule x1 ( cnt >= 1 && cnt < 10  ) ;
      shiftAmt <= shiftAmt  + 1 ;
      printv ( t1 ) ;
      let t = rotateBy( t1, shiftAmt ) ;
      $display ("\n\n Shifterd by %0d", shiftAmt ) ;
      t1 <= t ;      
   endrule
   
   Reg#(Bit#(128)) sdata <- mkReg ( 'had59 ) ;
   Reg#(UInt#(7)) sa2 <- mkReg(0) ;
   rule x2 ( cnt >= 11 && cnt < 30  ) ;
      sa2 <= sa2  + 1 ;
      let  t = rotateBitsBy( sdata, sa2 ) ;
      $display ("Shifted by %2d %h %h", sa2, sdata, t ) ;
      //sdata <= t ;      
   endrule

   
   Reg#(Bit#(5)) sdata5 <- mkReg ( 'b10011 ) ;
   Reg#(UInt#(3)) sa25 <- mkReg(0) ;
   rule x3 ( cnt >= 31 && cnt < 40  ) ;
      sa25 <= sa25  + 1 ;
      let  t = rotateBitsBy( sdata5, sa25 ) ;
      $display ("Shifted by %2d %b %b", sa25, sdata5, t ) ;
      //sdata5 <= t ;      
   endrule

endmodule

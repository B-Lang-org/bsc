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
module sysCountElem() ;
   
      
   Reg#(int) cnt <- mkReg(0) ;
   
   // countElem :: (Add 1 n n1, Add xxx 1 n, Log n1 lgn1, Eq a)  => a -> Vector n a -> UInt lgn1
   // countElem elem v = countIf ( (==) elem ) v   // findElem elem v = findIndex ( (==) elem ) v
   
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
      t[4] = x1 ;
      t[5] = x5 ;
      t[6] = x1 ;
      t[7] = x2 ;
      
      t1 <= t ;
   endrule

   rule x1 ( cnt == 1 ) ;
      printv ( t1 ) ;
      let t = t1 ;
      let f = countElem ( x1 , t1 );
      printBE( x1 ) ;
      $display ("%0d  x1 elements found", f ) ;

   endrule

   rule x2 ( cnt == 2 ) ;
      // printv ( t1 ) ;
      let t = t1 ;
      let f = countElem ( x2 , t1 );
      printBE( x2 ) ;
      $display ("%0d  x2 elements found", f ) ;

   endrule
   rule x3 ( cnt == 3 ) ;
      // printv ( t1 ) ;
      let t = t1 ;
      let f = countElem ( x3 , t1 );
      printBE( x3 ) ;
      $display ("%0d  x3 elements found", f ) ;

   endrule
   rule x4 ( cnt == 4 ) ;
      // printv ( t1 ) ;
      let t = t1 ;
      let f = countElem ( x4 , t1 );
      printBE( x4 ) ;
      $display ("%0d  x4 elements found", f ) ;

   endrule

endmodule

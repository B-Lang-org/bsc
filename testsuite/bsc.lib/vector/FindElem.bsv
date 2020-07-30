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
module sysFindElem ();
   
      
   Reg#(int) cnt <- mkReg(0) ;
   
   // findElem :: (Add xx1 1 n, Log n lgn, Eq a) => a -> Vector n a -> Maybe (UInt lgn)
   // findElem elem v = findIndex ( (==) elem ) v
   
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

   rule x1 ( cnt >= 1 && cnt < 3 ) ;
      printv ( t1 ) ;
      let t = t1 ;
      let f = findElem ( x2 , t1 );
      if ( f matches tagged Valid .indx )
         begin
            printBE ( t1[indx] ) ;
            $display ("Found x2  at index %d  setting to -1 , ", indx ) ;
            t = update( t, indx, xNull ) ;
         end
      else
         begin
            $display ( "did not find x2" ) ;
         end
      t1 <= t ;      
   endrule
   
   rule x2 ( cnt >= 3 && cnt < 5 ) ;
      printv ( t1 ) ;
      let t = t1 ;
      let f = findElem ( x3 , t1 );
      if ( f matches tagged Valid .indx )
         begin
            printBE ( t1[indx] ) ;
            $display ("Found x3  at index %d  setting to -1 , ", indx ) ;
            t = update( t, indx, xNull ) ;
         end
      else
         begin
            $display ( "did not find x3" ) ;
         end
      t1 <= t ;      
   endrule
   
   rule x3 ( cnt >= 5 && cnt < 7 ) ;
      printv ( t1 ) ;
      let t = t1 ;
      let f = findElem ( xNull , t1 );
      if ( f matches tagged Valid .indx )
         begin
            printBE ( t1[indx] ) ;
            $display ("Found xNull  at index %d  setting to -1 , ", indx ) ;
            t = update( t, indx, xNull ) ;
         end
      else
         begin
            $display ( "did not find xNull" ) ;
         end
      t1 <= t ;      
   endrule

   Reg#(Bit#(16))  br <- mkReg( 'hd673 ) ;
   
   rule countleading ( cnt > 80 ) ;
      UInt#(5) lz = countLeadingZeros( br ) ;
      UInt#(5) ones = countOnes( br );
      $display( "for: %b  lz = %0d     1's = %0d", br, lz, ones ) ;
      br <= (br << 4) ^ ( br >> 5 ) ;
   endrule
   
   
endmodule

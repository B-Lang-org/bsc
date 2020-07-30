typedef Bit#(25) Word;

// Find the bit position of the most significant non-zero bit.
// returns 0 if none is found, lsb is bit 1
function UInt#(k) msBit(Bit#(s) din)
;//   provisos ( Add#(sx,2,sk), Log#(sk, k) );

   let vectorSize = primValueOf ( din ) ;
   UInt#(k) res = 0 ;
   for( Integer i = (vectorSize - 1)  ; (res == 0) && (i > 0)  ;i = i - 1)
   begin
      Nat idx = fromInteger( i )  ;
//      if ( din[idx] == 1'b1 )  res = fromInteger( i ) ; else res = 0 ;
       if ( din[idx] == 1'b1 )  res = fromInteger( i + 1) ; else res = 0 ;
   end

   return res ;
   
endfunction

(* noinline *)
function UInt#(16) cmsb( Word din ) ;
   begin
      return msBit( din ) ;
   end
endfunction

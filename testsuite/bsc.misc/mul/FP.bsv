// A structure for holding a fixed-point number 
typedef struct {
                Int#(isize)  intPart ;
                UInt#(fsize)  fracPart ;
                }
FixedPoint#(type isize, type fsize )
deriving( Eq ) ;

instance Bits#( FixedPoint#(i,f), sizefp )
         provisos( Add#(i,f,sizefp) ) ;
   function Bit#(sizefp) pack( FixedPoint#(i,f)  fxpIn ) ;
      return { pack(fxpIn.intPart), pack(fxpIn.fracPart) } ;
   endfunction
   function FixedPoint#(i,f) unpack( Bit#(sizefp) bitIn );
      match { .ip, .fp } = Tuple2#(Bit#(i),Bit#(f))'( unpack( bitIn ) ) ;
      return FixedPoint{ intPart: unpack(ip), 
                        fracPart: unpack(fp) } ;
   endfunction
endinstance
//  We can derive Ord.  Later....

// Types within the Arith typeclass must have functions defined for +,
// -, negate and *.
instance Arith#( FixedPoint#(i,f) )  ;

   function \+ (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
      let in1p = pack(in1) ;
      let in2p = pack(in1) ;
      let sump = in1p + in2p ;
      return unpack( sump ) ;
                            
   endfunction
   
   function \- (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
      let in1p = pack(in1) ;
      let in2p = pack(in1) ;
      let sump = in1p - in2p ;
      return unpack( sump ) ;
                            
   endfunction
   
   function \* (FixedPoint#(i,f) in1, FixedPoint#(i,f) in2 );
      let in1p = pack(in1) ;
      let in2p = pack(in1) ;
      let sump = in1p + in2p ;
      return unpack( sump ) ;
                            
   endfunction
   
   function negate (FixedPoint#(i,f) in1 );
      let in1p = pack(in1) ;
      let sump = 0 - in1p  ;
      return unpack( sump ) ;
                            
   endfunction
   
endinstance

instance Literal#( FixedPoint#(i,f) ); 

   function fromInteger(n) ;
      return FixedPoint{ intPart: fromInteger(n), fracPart: 0 } ;
   endfunction
endinstance


// Full precision mult function
function FixedPoint#(ri,rf)  fxpMult( FixedPoint#(ai,af) a,
                                  FixedPoint#(bi,bf) b )
   provisos( Add#(ai,bi,ri),
            Add#(af,bf,rf),
            Add#(sa,sb,sr),
            Bits#(FixedPoint#(ri,rf),sr),
            Bits#(FixedPoint#(ai,af),sa),
            Bits#(FixedPoint#(bi,bf),sb)
            ) ;

   Bit#(sa)  in1p = pack(a) ;
   Bit#(sb)  in2p = pack(b) ;
   Bit#(sr)   seA = signExtend( in1p ) ;
   Bit#(sr)   seB = signExtend( in2p ) ;
   Bit#(sr)  prod = seA * seB ;
   FixedPoint#(ri,rf) res = unpack( prod ) ;
   return res ;

   
endfunction


//(* noinline *)
function FixedPoint#(1,15) testAdd115( FixedPoint#(1,15) a, FixedPoint#(1,15) b ) ;
   return  a + b  ;
endfunction

(* noinline *)
function FixedPoint#(2,15) testMult15( FixedPoint#(1,7) a, FixedPoint#(1,8) b ) ;
   return  fxpMult(a,b)  ;
endfunction


//function Bit#(n) fxpPack

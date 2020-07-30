package FPLibrary ;

typedef Bit#(32) IEEE754_32;
typedef Bit#(64) IEEE754_64;

typedef Bool FP_Sign ;
typedef Bit#(2)  FP_RS ;

typedef struct {
                FP_Sign    sign;// Sign bit
                Bit#(ee)   exp; // exponent 
                Bit#(ss)   sfd; // significand
                FP_RS      rs ; // round and sticky bit
                } FP_I #(type ee, type ss)
                deriving(Bits);



// extract out the fields from a 32 bit FP.   Handle zero exp correctly
function FP_I#(8,24) 
   extract_fields( IEEE754_32 din ) ;
   begin
      FP_Sign      sign   = unpack(din[31]) ;
      Bit#(8)      exp    = unpack( din[30:23]) ;
      Bit#(1)      hidden = ( exp != 0 ) ? 1'b1 : 1'b0 ;
      Bit#(24)    sfd    = ( {hidden, din[22:0] } );

      return FP_I{ sign:sign, exp:exp, sfd:sfd, rs:2'b00 } ;
   end
endfunction




// Take the structure and pack it into a IEEE FP format
function IEEE754_32
   pack_fields( FP_I#(8,24)  din ) ;
   begin
      // TODO Need to assert that "hidden" bit is 1 unless exp is 0.
      return { pack(din.sign), pack(din.exp), pack( truncate( din.sfd ))  } ;
   end
endfunction


// extract out the fields from a 32 bit FP.   Handle zero exp correctly
function FP_I#(10,54) 
   extract_fields64( IEEE754_64 din ) ;
   begin
      FP_Sign      sign   = unpack(din[63]) ;
      Bit#(10)     exp    = unpack( din[62:53]) ;
      Bit#(1)      hidden = ( exp != 0 ) ? 1'b1 : 1'b0 ;
      Bit#(54)     sfd    = ( {hidden, din[52:0] } );

      return FP_I{ sign:sign, exp:exp, sfd:sfd, rs:2'b00 } ;
   end
endfunction




// Take the structure and pack it into a IEEE FP format
function IEEE754_64
   pack_fields64( FP_I#(10,54)  din ) ;
   begin
      // TODO Need to assert that "hidden" bit is 1 unless exp is 0.
      return { pack(din.sign), pack(din.exp), pack( truncate( din.sfd ))  } ;
   end
endfunction


// Generate the rounds and stick bit based on the significand and shift amt
function FP_RS
   generate_rs( Bit#(s) sfd, Nat sftamt )
   provisos( Add#(a,1,s) ) ;
   begin
      // TODO need size of
      let vectorsize = fromInteger( primValueOf ( sfd )) ;
      let rev_shift = (sftamt <= vectorsize) ?
                      ( vectorsize - sftamt ) : 0;
      Bit#(s)  sfd1 = sfd << rev_shift ;

      // TODO !!! TODO  should use reduction or
      Bit#(s) sv =  { sfd1[vectorsize-2:0], 1'b0 } ;
      Bit#(1) sbit = (sv != 0 ) ? 1'b1: 1'b0 ;

      // Avoid X generation when off the array.
      Bit#(1) rbit = (sftamt <= vectorsize) ? sfd[(sftamt - 1):(sftamt - 1)] : 1'b0 ;
      return { rbit, sbit } ;
   end
endfunction

// perform rounding based on round and sticky bit.
// Takes an n-bit significand and returns a (n+1) bit significand
function FP_I#(e,s1) 
   round ( FP_I#(e, s) din ) 
   provisos( Add#( s, 1, s1)) ;
   begin
      Bit#(3) rbits = { din.sfd[0:0] , din.rs } ;
      Bit#(s1) sfdout = zeroExtend( din.sfd ) ;  
      FP_RS rsout = din.rs ;

      if (( rbits == 3 ) || ( rbits > 5 )) // round up at 3,6,7
         begin
            sfdout = zeroExtend( din.sfd ) + 1 ;
            rsout = { 1'b0, din.rs[0] }  ;  
         end
      else
         begin
            sfdout = zeroExtend( din.sfd ) ;  
            rsout = din.rs ;
         end      
   
      return FP_I{ sign:din.sign, exp:din.exp, sfd:sfdout, rs:rsout } ;
   end
endfunction


// Normalize the result, with a maximum disparity of 1.   this cannot be used
// after a subtractions, since the significand can be 0
function FP_I#(e,s)
   normalize1( FP_I#(e,s1) din ) 
   provisos( Add#(x, 2, s1),  Add#(s, 1, s1), Add#(a, 1, s) );
   begin
      Bit#(e) expout = 0;
      Bit#(s) sfdout = 0;
      FP_RS   rsout = 0;

      Tuple2#( Bit#(2), Bit#(x) ) splitbits = split ( din.sfd ) ;
      Bit#(2) carrymsb = tpl_1(splitbits) ;

      if ( 1 == carrymsb[1:1] )
         begin
            // TODO overflow can occur here
            expout = din.exp + 1 ;
            sfdout = truncate( din.sfd >> 1) ;
            rsout = {din.sfd[0], pack(din.rs != 0) } ;
         end
      else if ( din.exp == 0 )      // Denormalized case ??
         begin
            expout = din.exp;
            sfdout = truncate ( din.sfd );
            rsout  = 2'b00 ;
         end
      else if ( 1 == carrymsb[0:0] ) // The sum is in normalized form
         begin
            expout = din.exp;
            sfdout = truncate( din.sfd ) ;
            rsout  = din.rs ;
         end
      else
         begin                  // left shift by 1
            // TODO for subtract this can be a multi bit shift.
            expout = din.exp - 1 ;
            let vectorsize = fromInteger( primValueOf ( din.sfd )) ;
            sfdout = {din.sfd[vectorsize-3:0] ,  din.rs[0:0] } ;
            rsout  = {1'b0, din.rs[0:0] };
         end
      
      return FP_I{ sign:din.sign, exp:expout, sfd:sfdout, rs:rsout } ;        
   end
endfunction

// Normalize the result, with a maximum disparity of 1.   this cannot be used
// after a subtractions, since the significand can be 0
function FP_I#(e,s)
   normalize( FP_I#(e,s1) din ) 
   provisos( 
             Add#(s, 1, s1),    // basic relation
             Add#(x0, 1, s),     // s is at least 1 bit 
             Add#(x1, 2, s1),   // Needed for split
             Add#(x2, e, 32),   // e is less than or equal to 32 (limit on shift op) (e <= 32)
             Add#(x4, TLog#(TAdd#(s1,1)), e ),  // log(s+2) <= e
            Add#(0, TLog#(TAdd#(s1,1)), ms ),
             Log#( TAdd#(s1,1), TLog#(TAdd#(s1,1))),
             Add#( s1, 1, TAdd#(s1,1)),
             Add#(x3, ms, e)    // We can extend the findmsb result to e. (e >= ms)
            );
   begin
      Bit#(e) expout = 0;
      Bit#(s) sfdout = 0;
      FP_RS   rsout = 0;

      Tuple2#( Bit#(2), Bit#(x1) ) splitbits = split ( din.sfd ) ;
      Bit#(2) carrymsb = tpl_1(splitbits) ;

      if ( 1 == carrymsb[1:1] )
         begin
            // TODO overflow can occur here
            expout = din.exp + 1 ;
            sfdout = truncate( din.sfd >> 1) ;
            rsout = {din.sfd[0], pack(din.rs != 0) } ;
         end
      else if ( din.exp == 0 )      // Denormalized case ??
         begin
            expout = din.exp;
            sfdout = truncate ( din.sfd );
            rsout  = 2'b00 ;
         end
      else if ( 1 == carrymsb[0:0] ) // The sum is in normalized form
         begin
            expout = din.exp;
            sfdout = truncate( din.sfd ) ;
            rsout  = din.rs ;
         end
      else
         begin                  // left shift by N bits
            Bit#(ms) msba = findmsb( din.sfd ) ;
            Bit#(e) msb = zeroExtend( msba ) ;
            if ( msb == 0 )
               begin
                  expout = 0 ;
                  sfdout = 0 ;
                  rsout  = 2'b00 ;
               end
            else
               begin
                  Bit#(e) vectorSize = fromInteger( primValueOf ( din.sfd )) ;
                  Bit#(e) sftamt = (vectorSize - 1) - msb ;
                  
                  sfdout = truncate( din.sfd << sftamt ) ;
                  // TODO underflow 
                  expout = din.exp - sftamt ; 
                  rsout  = {1'b0, din.rs[0:0] };
               end
         end
      
      return FP_I{ sign:din.sign, exp:expout, sfd:sfdout, rs:rsout } ;        
   end
endfunction


// Find the bit position of the most significant non-zero bit.
// returns 0 if none is found, lsb is bit 1
function Bit#(k) findmsb(Bit#(s) din)
   provisos ( Add#(s,1,sk), Log#(sk, k) );

   let vectorSize = primValueOf ( din ) ;
   Bit#(k)  res = 0 ;
   for( Integer i = 0 ; (i < vectorSize)  ;i = i + 1)
   begin
      Nat idx = fromInteger( i )  ;
      if ( din[idx:idx] == 1'b1 )  res = fromInteger( i + 1 ) ;  else res = res ;
   end

   return res ;

endfunction

endpackage

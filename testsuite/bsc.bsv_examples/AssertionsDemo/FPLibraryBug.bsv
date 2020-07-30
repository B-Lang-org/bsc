typedef Bit#(32) IEEE754_32;
typedef Bit#(64) IEEE754_64;

typedef Bool FP_Sign ;
typedef Bit#(2)  FP_RS ;

function Bit#(1) topBit(Bit#(n) vector) provisos (Add#(m,1,n));
  return(vector[(fromInteger(valueof(m)))]);
endfunction

// Floating point internal representation
typedef struct {
                FP_Sign    sign;// Sign bit
                Bit#(ee)   exp; // exponent 
                Bit#(ss)   sfd; // significand
                FP_RS      rs ; // round and sticky bit
                } FP_I
                  #(type ee, type ss) // exponent and significand sizes are parameters
                  deriving(Bits);

//Note that the FP_I structure is often used with 2 sizes in many function
// i.e., FP_I#(e,s) and FP_I#(e,s1)
// In the FP_I#(e,s) format, the binary point is assumed immediately after
// MSB, in the FP_I#(e,s1) format, the binary point is after the second bit.
// This convention allows FP_I#(e,s) + FP_I#(e,s) to yield FP_I#(e,s1)


FP_I#(ee, ss) fpi_zero = unpack(0);

// extract out the fields from a 32 bit FP. 
function FP_I#(8,24) 
   extract_fields( IEEE754_32 din ) ;
   begin
      FP_Sign      sign   = unpack(din[31]) ;
      Bit#(8)      exp    = din[30:23] ;
      Bit#(1) hidden = 0;
//      Bit#(1)      hidden = exp != 0  ? 1'b1 : 1'b0 ;
      Bit#(24)     sfd    = {hidden, din[22:0] } ;

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


// extract out the fields from a 64 bit IEEE FP. 
function FP_I#(11,53) 
   extract_fields64( IEEE754_64 din ) ;
   begin
      FP_Sign      sign   = unpack(din[63]) ;
      Bit#(11)     exp    = din[62:52] ;
      Bit#(1) hidden = 0;    
//      Bit#(1)      hidden = ( exp != 0 ) ? 1'b1 : 1'b0 ;
      Bit#(53)     sfd    = ( {hidden, din[51:0] } );

      return FP_I{ sign:sign, exp:exp, sfd:sfd, rs:2'b00 } ;
   end
endfunction




// Take the structure and pack it into a IEEE 64 bit FP format
function IEEE754_64
   pack_fields64( FP_I#(11,53)  din ) ;
   begin
      // TODO Need to assert that "hidden" bit is 1 unless exp is 0.
      return { pack(din.sign), pack(din.exp), pack( truncate( din.sfd ))  } ;
   end
endfunction


// Generate the rounds and sticky bit based on the significand and shift amt
// function is used during addition operations
function FP_RS
   generate_rs( Bit#(s) sfd, Nat sftamt )
   provisos( Add#(a,1,s) ) ;
   begin
      let vectorsize = fromInteger( primValueOf ( sfd )) ;
      let rev_shift = (sftamt <= vectorsize) ?
                      ( vectorsize - sftamt ) : 0;
      Bit#(s)  sfd1 = sfd << rev_shift ;

      Bit#(s) sv =  { sfd1[vectorsize-2:0], 1'b0 } ;
      Bit#(1) sbit = | sv ; 

      // Avoid X generation when off the array.
      Bit#(1) rbit = (sftamt <= vectorsize) ? sfd1[vectorsize-1] : 1'b0 ;
      return { rbit, sbit } ;
   end
endfunction

// perform rounding based on round and sticky bit.
// Takes an n-bit significand and returns a (n+1) bit significand
function FP_I#(e,s1) 
   round ( FP_I#(e, s) din ) 
   provisos( Add#( s, 1, s1)) ;
   begin
      Bit#(3) rbits = { din.sfd[0] , din.rs } ;
      Bit#(s1) sfdout = zeroExtend( din.sfd ) ;  
      FP_RS rsout = din.rs ;

      if (( rbits == 3 ) || ( rbits > 5 )) // round up at 3,6,7
         begin
            sfdout = zeroExtend( din.sfd ) + 1 ;
            rsout = { 1'b0, din.rs[0] }  ;  
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

      if ( 1 == carrymsb[1] )
         begin
            // TODO overflow can occur here
            expout = din.exp + 1 ;
            sfdout = truncate( din.sfd >> 1) ;
            rsout = {din.sfd[0], pack(din.rs != 0) } ;
         end
      else if ( din.exp == 0 )      // Denormalized case -- do not modify
         begin
            expout = din.exp;
            sfdout = truncate ( din.sfd );
            rsout  = 2'b00 ;
         end
      else if ( 1 == carrymsb[0] ) // The sum is in normalized form
         begin
            expout = din.exp;
            sfdout = truncate( din.sfd ) ;
            rsout  = din.rs ;
         end
      else
         begin                  // left shift by 1
            expout = din.exp - 1 ;
            let vectorsize = fromInteger( primValueOf ( din.sfd )) ;
            sfdout = {din.sfd[vectorsize-3:0] ,  din.rs[0] } ;
            rsout  = {1'b0, din.rs[0] };
         end
      
      return FP_I{ sign:din.sign, exp:expout, sfd:sfdout, rs:rsout } ;        
   end
endfunction

// Normalize the result, allowing left shifts on N positions
function FP_I#(e,s)
   normalize( FP_I#(e,s1) din ) 
   provisos( 
             Add#(s, 1, s1),    // basic relation
             Add#(x0, 1, s),     // s is at least 1 bit 
             Add#(x1, 2, s1),   // Needed for split
             Add#(x2, e, 32)    // e is less than or equal to 32 (limit on shift op) (e <= 32)
            );
   begin
      Bit#(e) expout = 0;
      Bit#(s) sfdout = 0;
      FP_RS   rsout = 0;

      Tuple2#( Bit#(2), Bit#(x1) ) splitbits = split ( din.sfd ) ;
      Bit#(2) carrymsb = tpl_1(splitbits) ;

      if ( 1 == carrymsb[1] )
         begin
            // TODO overflow can occur here
            expout = din.exp + 1 ;
            sfdout = truncate( din.sfd >> 1) ;
            rsout = {din.sfd[0], pack(din.rs != 0) } ;
         end
      else if ( din.exp == 0 )      // Denormalized case
         begin
            expout = din.exp;
            sfdout = truncate ( din.sfd );
            rsout  = 2'b00 ;
         end
      else if ( 1 == carrymsb[0] ) // The sum is in normalized form
         begin
            expout = din.exp;
            sfdout = truncate( din.sfd ) ;
            rsout  = din.rs ;
         end
      else
         begin                  // left shift by N bits
            Bit#(e) msb = truncate( findmsb( din.sfd ) ) ;
            if ( msb == 0 )     // zero result
               begin
                  expout = 0 ;
                  sfdout = 0 ;
                  rsout  = 2'b00 ;
               end
            else
               begin
                  Bit#(e) vectorSize = fromInteger( primValueOf ( din.sfd )) ;
                  Bit#(e) sftamt = (vectorSize - 1) - msb ;
                  
                  sfdout = truncate( din.sfd <<  sftamt ) ;
                  // TODO underflow 
                  expout = din.exp - sftamt ; 
                  rsout  = {1'b0, din.rs[0] };
               end
         end
      
      return FP_I{ sign:din.sign, exp:expout, sfd:sfdout, rs:rsout } ;        
   end
endfunction


// Find the bit position of the most significant non-zero bit.
// returns 0 if none is found, lsb is bit 1
function Nat findmsb(Bit#(s) din);

   let vectorSize = primValueOf ( din ) ;
   Nat res = 0 ;
   for( Integer i = 0 ; (i < vectorSize)  ;i = i + 1)
   begin
      Nat idx = fromInteger( i )  ;
      if ( din[idx] == 1'b1 )  res = fromInteger( i + 1 ) ;  else res = res ;
   end

   return res ;

endfunction

// Negate -- change the sign of the data.
function FP_I#(e,s) negate ( FP_I#(e,s) din );
   din.sign = ! din.sign ;
   return din ;
endfunction


// Absolute value -- Sign bit to false
function FP_I#(e,s) abs ( FP_I#(e,s) din );
   din.sign = False ;
   return din ;
endfunction


// Return True if dinA less than dinB 
function  Bool lessthan  ( FP_I#(e,s) inA, FP_I#(e,s) inB );
   let signLT = ( inA.sign && ! inB.sign ) ;
   let signEQ = inA.sign == inB.sign ;
   let expLT  = inA.exp  < inB.exp ;
   let expEQ  = inA.exp == inB.exp ;
   let sfdLT  = inA.sfd < inB.sfd ;
   return ( signLT ||
           (signEQ && expLT ) ||
           (signEQ && expEQ && sfdLT ) );           
endfunction

// normalize and truncate the significand from sx bit to s bits
// The first argument specifies where the binary point is relative to the msb side
// e.g., 0 implies that poisition is normal X.xxx, 1 implies XX.xxx, etc.
function FP_I#(e,s)
   normalize_and_truncate( Bit#(e) binaryPointPosition, FP_I#(e,sx) din ) 
   provisos(
            Add#(s,a,sx ),
            Add#(sx,1,sx1 ),
            Add#(a,1,a1 ),
            Add#(s,a1,sx1),
            Add#(e,nn,32)
            );
   begin
      Bit#(s) sfdout = 0 ;
      Bit#(e) expout = 0 ;
      FP_RS    rsout = 0 ;
      Bit#(1) rndbit = din.rs[1] ;
      Bit#(1) stkybit = din.rs[0] ;

      Nat msb = findmsb(  din.sfd ) ;
      Bit#(a1) rest = 0 ;

      // Default conditions are set for 0 result.
      if ( msb != 0 )
         begin
            let vectorSize = fromInteger( primValueOf ( din.sfd )) ;
            let sftamt = vectorSize - msb ;
            Bit#(sx1) sfdfull = { din.sfd, rndbit } << sftamt ;
            {sfdout, rest} = split( sfdfull ) ;

            // Adjust exponent -- taking into account where the binary point was
            expout = binaryPointPosition + din.exp - truncate( sftamt ) ;
            // TODO handle underflow, overflow

            // Calculate the round and sticky bits
            Tuple2#( Bit#(1), Bit#(a) ) { rnd, stky } = split( rest ) ;
            rsout = { rnd, (| stky) | stkybit  } ;

         end

      return FP_I{ sign:din.sign, exp:expout, sfd:sfdout, rs:rsout } ;
   end
endfunction

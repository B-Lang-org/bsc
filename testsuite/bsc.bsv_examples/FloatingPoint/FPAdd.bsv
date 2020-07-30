// TODO:
//    overflow, underflow
//    NAN


package FPAdd;

import FPLibrary::* ;
import TesterLib::*;


// normalize the significands based on the exponent difference.
// and add
function FP_I#(e,s1)
   match_exp_add ( FP_I#(e,s) inA, FP_I#(e,s) inB )
   provisos( Add#(s, 1, s1),
             Add#(e, x, 32),// e must be less than 32 so it can be extended
             Add#(y, 1, s )
            ) ;   
   begin

      Bit#(s) outa = 0;
      Bit#(s) outb = 0;
      Bit#(e) outexp = 0 ;

      FP_Sign outsign ;
      FP_RS   rsa ;
      Nat     diffamt ;

      if ( inA.exp > inB.exp )           // A > B
         begin
            outa    = inA.sfd ;
            outb    = inB.sfd ; 
            diffamt = zeroExtend( inA.exp - inB.exp );
            outsign = inA.sign ;
            outexp  = inA.exp ;
            rsa     = inA.rs ;
         end
      else if ( inB.exp > inA.exp )       // B > A 
         begin
            outa    = inB.sfd ;
            outb    = inA.sfd ;
            diffamt = zeroExtend( inB.exp - inA.exp );
            outsign = inB.sign ;
            outexp  = inB.exp ;
            rsa     = inB.rs ;
         end
      else if ( inA.sfd > inB.sfd )     // A > B
         begin
            outa    = inA.sfd;
            outb    = inB.sfd;
            diffamt = 0 ;            
            outsign = inA.sign ;
            outexp  = inA.exp ;
            rsa     = inB.rs ;
         end
      else
         begin
            outa    = inB.sfd;
            outb    = inA.sfd;
            diffamt = 0 ;            
            outsign = inB.sign ;
            outexp  = inA.exp ;
            rsa     = inA.rs ;
         end

      // Shifting and extending
      let eoutb = outb >> diffamt ;

      // generate round and sticky
      FP_RS rsb = generate_rs( outb, diffamt ) ;
      
      // now do the addition or subtractions on the normalized significand
      Bit#(s1) outv = 0;
      Bit#(s1) roundbit ;
      FP_RS    rsout ;
      if (inB.sign == inA.sign)
         begin
            roundbit = unpack(rsa[1] & rsb[1]) ? 1 : 0 ;
            outv     = zeroExtend( outa ) + zeroExtend( eoutb) + roundbit ;
         end
      else
         begin
            roundbit = unpack(rsa[1] &  ~rsb[1]) ? 1 : 0 ;            
            outv     = zeroExtend( outa ) - zeroExtend( eoutb ) + roundbit ;
         end
      rsout = { rsa[1] ^ rsb[1], rsa[0] | rsb[0] } ;
      
      return FP_I{ sign:outsign, exp:outexp, sfd:outv, rs:rsout } ;      
   end
endfunction


function FP_I#(e,s1)
   match_exp_sub ( FP_I#(e,s) inA, FP_I#(e,s) inB )
   provisos( Add#(s, 1, s1),
             Add#(e, x, 32),
             Add#(y, 1, s )
            ) ;   // e must be less than 32 so it can be extended
   begin
      let inBN  = negate( inB ) ;
      return match_exp_add( inA, inBN ) ;
   end
endfunction



// Top-level FP 32 add function.
function IEEE754_32
   fpAdd( IEEE754_32 inA, IEEE754_32 inB );
   begin
      let inAE = extract_fields( inA );
      let inBE = extract_fields( inB ) ;

      let bas_res =
          match_exp_add( inAE, inBE  ) ;
   
      // normalize, round, normalize
      let norm1 = normalize_and_truncate( 1, bas_res ) ;
      let rounded = round ( norm1 ) ;
      let normed_result = normalize1( rounded ); // Max of 1 bit normalization

      return pack_fields( normed_result ) ;
   end
endfunction



// Top-level FP add function.
function IEEE754_64
   fpAdd64( IEEE754_64 inA, IEEE754_64 inB );
   begin
      let inAE = extract_fields64( inA );
      let inBE = extract_fields64( inB ) ;

      let bas_res =
          match_exp_add( inAE, inBE  ) ;
   
      // normalize, round, normalize
      let norm1 = normalize_and_truncate( 1, bas_res ) ;
      let rounded = round ( norm1 ) ;
      let normed_result = normalize1( rounded ); // Max of 1 bit normalization

      return pack_fields64( normed_result ) ;
   end
endfunction



(* synthesize *)
// Create a module which has QBinOp (32 bit) interface, and fpAdd function
module mkFPAdd (QBinOp #(IEEE754_32) ) ;

   QBinOp #(IEEE754_32) ifc() ;
   mkFPBinOp#(fpAdd) dut(ifc) ;

   return ifc ;
endmodule


(* synthesize *)
// Create a module which has QBinOp (64 bit) interface, and fpAdd64 function
module mkFPAdd64 (QBinOp #(IEEE754_64) ) ;

   QBinOp #(IEEE754_64) ifc() ;
   mkFPBinOp#(fpAdd64) dut(ifc) ;

   return ifc ;
endmodule



endpackage

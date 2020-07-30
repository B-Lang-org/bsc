package FPMult;

import FPLibrary::*;
import TesterLib::*;

// A general function to multiple 2 FP number
function FP_I#(e,s1) multfp ( FP_I#(e,s) inA, FP_I#(e,s) inB )
   provisos( Add#(s, 1, s1),
             Add#(x1, 2, s),
             Add#(x2, 3, s),
             Add#(s, s, ss )
            );
   begin
      let bias   = fromInteger( exp( 2, (primValueOf ( inA.exp ) - 1)) - 1) ;
      let opSize = fromInteger( primValueOf ( inA.sfd )) ;
      
      FP_Sign signout = inA.sign != inB.sign ;
      // TODO check for overflow
      let expout = ((inA.exp != 0) && (inB.exp != 0 )) ?
                             inA.exp + inB.exp - bias : 0 ;

      Bit#(ss) multout  = primMul( inA.sfd, inB.sfd ) ;
      Bit#(s1) sfdout   = multout[(opSize+opSize)-1:opSize-1] ;
      Bit#(x1) stickies = multout[opSize-3:0] ;
      Bit#(1)  sticky   = (stickies != 0) ? 1'b1 : 1'b0  ;
      FP_RS    rsout    = {multout[opSize-2], sticky } ;

      return FP_I{ sign:signout, exp:expout, sfd:sfdout, rs:rsout } ;
   end
endfunction


// A general function to multiple 2 FP number and leave the result in extended precision
// in the significand.
function FP_I#(e,sx) multfp_eprecision ( FP_I#(e,s) inA, FP_I#(e,s) inB )
   provisos( Add#(s, s, sx),
             Add#(x1, 2, s),
             Add#(x2, 3, s)
            );
   begin
      let bias   = fromInteger( exp( 2, (primValueOf ( inA.exp ) - 1)) - 1) ;
      let opSize = fromInteger( primValueOf ( inA.sfd )) ;
      
      FP_Sign signout = inA.sign != inB.sign ;
      // TODO check for overflow
      let expout = ((inA.exp != 0) && (inB.exp != 0 )) ?
                             inA.exp + inB.exp - bias : 0 ;

      Bit#(sx) multout  = primMul( inA.sfd, inB.sfd ) ;

      FP_RS    rsout    = 0 ;

      return FP_I{ sign:signout, exp:expout, sfd:multout, rs:rsout } ;
   end
endfunction



// a IEEE FP 32 bit multiplier 
function IEEE754_32
   fpMult( IEEE754_32 inA, IEEE754_32 inB ) ;
   begin
      let inAE = extract_fields( inA );
      let inBE = extract_fields( inB ) ;

      let bas_res =
          multfp( inAE, inBE  ) ;
      
      // normalize, round, normalize
      let norm1   = normalize1( bas_res ) ;
      let rounded = round ( norm1 ) ;
      let result  = normalize1( rounded );

      return pack_fields( result ) ;
   end
endfunction

// a IEEE FP 32 bit multiplier 
function IEEE754_64
   fpMult64( IEEE754_64 inA, IEEE754_64 inB ) ;
   begin
      let inAE = extract_fields64( inA );
      let inBE = extract_fields64( inB ) ;

      let bas_res =
          multfp( inAE, inBE  ) ;
      
      // normalize, round, normalize
      let norm1 = normalize1( bas_res ) ;
      let rounded = round ( norm1 ) ;
      let normed_result = normalize1( rounded );

      return pack_fields64( normed_result ) ;
   end
endfunction


// make a module with the fpmult (32) function and an added interface
(* synthesize *)
module mkFPMult (QBinOp #(IEEE754_32) ) ;

   QBinOp #(IEEE754_32) ifc() ;
   mkFPBinOp#(fpMult) dut(ifc) ;

   return ifc ;
endmodule


// make a module with the fpmult (64) function and an added interface
(* synthesize *)
module mkFPMult64 (QBinOp #(IEEE754_64) ) ;

   QBinOp #(IEEE754_64) ifc() ;
   mkFPBinOp#(fpMult64) dut(ifc) ;

   return ifc ;
endmodule

endpackage

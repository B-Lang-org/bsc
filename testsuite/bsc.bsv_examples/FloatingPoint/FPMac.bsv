// Multiple and accumulate unit 
package FPMac ;

import TesterLib::*;
import FPLibrary::*;
import FPAdd::*;
import FPMult::*;



// An implementation of a 32 bit mac (A*B) + C  unit 
function IEEE754_32 fpMac( IEEE754_32 inA, IEEE754_32 inB, IEEE754_32 inC ) ;
   begin
      let inAE = extract_fields( inA );
      let inBE = extract_fields( inB ) ;
      let inCE = extract_fields( inC ) ;

      let prod     = multfp( inAE, inBE  ) ;
      let normprod = normalize1( prod ) ;
      let mac      = match_exp_add( normprod, inCE  ) ;

      let normmac  = normalize1( mac ) ;
      let rounded  = round ( normmac ) ;
      let result   = normalize1( rounded );

      return pack_fields( result ) ;   

   end
endfunction

// An implementation of a 64 bit mac unit 
function IEEE754_64 fpMac64( IEEE754_64 inA, IEEE754_64 inB, IEEE754_64 inC ) ;
   begin
      let inAE = extract_fields64( inA );
      let inBE = extract_fields64( inB ) ;
      let inCE = extract_fields64( inC ) ;

      let prod     = multfp( inAE, inBE  ) ;
      let normprod = normalize1( prod ) ;
      let mac      = match_exp_add( normprod, inCE  ) ;

      let normmac  = normalize1( mac ) ;
      let rounded  = round ( normmac ) ;
      let result   = normalize1( rounded );

      return pack_fields64( result ) ;   

   end
endfunction


// An implementation of a 32 bit mac (A*B) - (C*D)  unit
// where results of product are represented in 48 bits.
(* noinline *)
function IEEE754_32 fpABlessCD( IEEE754_32 inA, IEEE754_32 inB,
                          IEEE754_32 inC, IEEE754_32 inD ) ;
   begin
      let inAE = extract_fields( inA );
      let inBE = extract_fields( inB ) ;
      let inCE = extract_fields( inC ) ;
      let inDE = extract_fields( inD ) ;

      let prodAB     = multfp_eprecision( inAE, inBE  ) ;
      let prodCD     = multfp_eprecision( inCE, inDE  ) ;
      // Binary point at position 2

      // do the subtract in extended precision
      let mac        = match_exp_sub( prodAB, prodCD ) ;
      // mac result is 49 bits need to truncate

      let binaryPoint = 2;
      let norm1 = normalize_and_truncate( binaryPoint, mac );
      
      let rounded  = round ( norm1 ) ;
      let result   = normalize1( rounded );

      return pack_fields( result ) ;   

   end
endfunction



// modules for testing
(* synthesize *)
module mkFPMac ( QTerOp #(IEEE754_32)) ;

   QTerOp #(IEEE754_32) ifc() ;
   mkFPTerOp#(fpMac) dut(ifc) ;

   return ifc ;
endmodule


(* synthesize *)
module mkFPMac64 ( QTerOp #(IEEE754_64)) ;

   QTerOp #(IEEE754_64) ifc() ;
   mkFPTerOp#(fpMac64) dut(ifc) ;

   return ifc ;
endmodule


endpackage

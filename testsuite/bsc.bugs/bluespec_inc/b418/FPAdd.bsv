// TODO:
//    overflow, underflow
//    NAN
//    generalize type signatures
//    extend for 64 bit


package FPAdd;

import FPLibrary::* ;
import FIFO::* ;



// normalize the signficands based on the exponent difference.
// and apply add or sub operation.
function FP_I#(e,s1)
   match_exp_add ( FP_I#(e,s) inA, FP_I#(e,s) inB )
   provisos( Add#(s, 1, s1),
             Add#(e, x, 32),
             Add#(y, 1, s )
            ) ;   // e must be less than 32 so it can be extended
   begin

      Bit#(s)   outa = 0;
      Bit#(s)   outb = 0;
      Bit#(e)   outexp = 0 ;

      FP_Sign outsign = True ;
      FP_RS rsa = 0;
      Nat diffamt = 0;

      if ( inA.exp > inB.exp )           // A > B
         begin
            outa = inA.sfd ;
            outb = inB.sfd ;
            diffamt = zeroExtend( inA.exp - inB.exp );
            outsign = inA.sign ;
            outexp = inA.exp ;
            rsa = inA.rs ;
         end
      else if ( inB.exp > inA.exp )       // B > A
         begin
            outa = inB.sfd ;
            outb = inA.sfd ;
            diffamt = zeroExtend( inB.exp - inA.exp );
            outsign = inB.sign ;
            outexp = inB.exp ;
            rsa = inB.rs ;
         end
      else if ( inA.sfd > inB.sfd )     // A > B
         begin
            outa = inA.sfd;
            outb = inB.sfd;
            diffamt = 0 ;
            outsign = inA.sign ;
            outexp = inA.exp ;
            rsa = inB.rs ;
         end
      else
         begin
            outa = inB.sfd;
            outb = inA.sfd;
            diffamt = 0 ;
            outsign = inB.sign ;
            outexp = inA.exp ;
            rsa = inA.rs ;
         end

      // Shifting and extending
      let eoutb = outb >> diffamt ;

      // TODO generate round and sticky
      FP_RS rsb = generate_rs( outb, diffamt ) ;

      // now do the addition or subtractions on the normalized significand
      Bit#(s1)  outv = 0;
      Bit#(s1) roundbit = 0 ;
      FP_RS rsout = 0;
      if (inB.sign == inA.sign)
         begin
            roundbit = unpack(rsa[1:1] & rsb[1:1]) ? 1 : 0 ;
            outv = zeroExtend( outa ) + zeroExtend( eoutb) + roundbit ;
         end
      else
         begin
            roundbit = unpack(rsa[1:1] &  ~rsb[1:1]) ? 1 : 0 ;
            outv = zeroExtend( outa ) - zeroExtend( eoutb ) + roundbit ;
         end
      rsout = { rsa[1:1] ^ rsb[1:1], rsa[0:0] | rsb[0:0] } ;

      return FP_I{ sign:outsign, exp:outexp, sfd:outv, rs:rsout } ;
   end
endfunction






// Top-level FP add function.
function IEEE754_32
   fpAdd( IEEE754_32 inA, IEEE754_32 inB );
   begin
      let inAE = extract_fields( inA );
      let inBE = extract_fields( inB ) ;

      let bas_res =
          match_exp_add( inAE, inBE  ) ;

      // normalize, round, normalize
      let norm1 = normalize( bas_res ) ;
      let rounded = round ( norm1 ) ;
      let normed_result = normalize1( rounded ); // Max of 1 bit normalization

      return pack_fields( normed_result ) ;
   end
endfunction



interface QBinOp #(parameter type a);
   method Action start( a inA, a inB );
   method a result();
   method Action deq () ;
endinterface

(* synthesize *)
module mkFPAdd (QBinOp #(IEEE754_32) ) ;
   QBinOp #(IEEE754_32) ifc() ;
   mkFPBinOp#(fpAdd) dut(ifc) ;

   return ifc ;
endmodule


module mkFPBinOp #( function IEEE754_32 fun ( IEEE754_32 a, IEEE754_32 b)) (QBinOp #(IEEE754_32) ) ;

   FIFO#(IEEE754_32) outfifo() ;
   mkFIFO i_outfifo(outfifo) ;

   FIFO#(Tuple2#(IEEE754_32, IEEE754_32)) infifo() ;
   mkFIFO i_infifo(infifo) ;

   rule crunch (True) ;
      action
         Tuple2#(IEEE754_32, IEEE754_32) pair = infifo.first ;
         infifo.deq ;
         outfifo.enq( fun( tpl_1(pair), tpl_2(pair) ) ) ;
      endaction
   endrule


   method start( inA, inB );
      action
         infifo.enq( tuple2( inA, inB ) ) ;
      endaction
   endmethod

   method result() ;
      return outfifo.first ;
   endmethod

   method deq() ; action
      outfifo.deq ;
   endaction endmethod

endmodule


/////////////////////////////////////////////////MAC Unit
interface QTerOp #(parameter type a);
   method Action start3( a inA, a inB, a inC );
   method a result();
   method Action deq () ;
endinterface

endpackage

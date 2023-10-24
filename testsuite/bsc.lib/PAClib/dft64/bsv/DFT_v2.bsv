

import PAClib::*;
import Complex::*;
import Vector::*;
import FixedPoint::*;
import FixedPointIO::*;
import ClientServer :: *;
import GetPut::*;
import FIFOF::*;
import Utils::*;
import DFTCoef::*;

import DFT::*;


Pipe#(CDPair, DX_t) mkMULTPIPE = usePipelinedMult ? mkCMultPipeline : mkCMultPipe;


//////////////////////////////////////////////////////////////////////////
// Function to generate a Vector of Vector of for coef permutations
function Vector# (n, Vector#(n, UInt#(TLog#(n)))) genPermIndex ();
   Integer nint = valueOf(n);
   function UInt#(TLog#(n)) genCoef_k_n (Integer k, Integer n);
      return fromInteger (k*n % nint);
   endfunction
   function Vector#(n, UInt#(TLog#(n))) genCoef_k (Integer k);
      return genWith (genCoef_k_n(k));
   endfunction
   return genWith(genCoef_k);
endfunction

// function to give select permuted data
function Vector# (n, t) getPermutedValue (Vector#(n, t) vin, UInt# (TLog#(n)) idx) ;
   Vector#(n, Vector#(n, UInt#(TLog#(n)))) permutations = genPermIndex();
   Vector#(n, UInt# (TLog#(n))) thisPerm = permutations[idx];
   return map (select (vin), thisPerm );
endfunction


// Create a Pipe element to generate all the coefficient
module [Module] mkCoefPerm (PipeOut#(VCoef_t));
   Integer nint = valueOf(NPoints);
   PipeOut#(VCoef_t) csrc <- mkSource_from_constant (coef_src);
   PipeOut#(VCoef_t) pout <- mkReplicateFn (nint, getPermutedValue, csrc);
   return pout;
endmodule

// Create a Pipe element to generate N copies of Data Set
module [Module] mkDataSetCopy (PipeOut# (VData_t) pin, PipeOut#(VData_t) pout);
   Integer nint = valueOf(NPoints);
   // provide replicate function keep the type checker happy
   function VData_t repeatFn (VData_t vin, UInt#(TLog#(NPoints)) idx) = vin;
   PipeOut#(VData_t)  pout <- mkReplicateFn (nint, repeatFn, pin);
   return pout;
endmodule


// Vector multiplication
// Another utility function to help  PAClib's mkMap_fn_with_funnel_indexed
function Complex#(DXFP_t) comb_mult(CDPair x);
   let vpp = complex_partialProducts (x);
   Vector#(4, DXFP_prod_t) truncated = map ( (fxptTruncateRoundSat(rndMode, satMode)), vpp);
   Vector#(4, DXFP_t)      extended  = map (  fxptSignExtend, truncated);

   // No overflow due to extended, hence no saturation needed
   return complex_partialProductsAdd(Sat_Wrap, extended);
endfunction

// complex multiple pipe
module [Module] mkCMultPipe ( PipeOut#(CDPair) vin, PipeOut#(Complex#(DXFP_t)) pout);
   let x <- mkFn_to_Pipe_Buffered(False, comb_mult, True, vin);
   return x;
endmodule

// A pipelined complex multiplier
function Vector#(4,FixedPoint#(ri,rf)) complex_partialProducts (Tuple2#(Complex# (FixedPoint#(ai,af)),
                                                                        Complex# (FixedPoint#(bi,bf)) ) x )
    provisos (Min#(ai, 1, 1)
             ,Min#(bi, 1, 1)
             ,Add#(ai,bi,ri)   // ri = ai + bi
             ,Add#(af,bf,rf)   // rf = af + bf
             ,Add#(ai,af,ab)
             ,Add#(bi,bf,bb)
             ,Add#(ab,bb,rb)
             ,Add#(ri,rf,rb)
            ) ;

   match {.c, .d} = x ;
   Vector#(4,FixedPoint#(ri,rf)) res = ? ;
   res[0] = fxptMult(c.rel, d.rel);
   res[1] = fxptMult(c.img, d.img);
   res[2] = fxptMult(c.rel, d.img);
   res[3] = fxptMult(c.img, d.rel);
   return res;
endfunction

function Complex #(FixedPoint#(ai,af)) complex_partialProductsAdd (SaturationMode smode
                                                                  ,Vector#(4,FixedPoint#(ai,af)) vt);
   return Complex { rel: satMinus (smode, vt[0], vt[1])
                   ,img: satPlus  (smode, vt[2], vt[3]) };
endfunction

module [Module] mkCMultPipeline (PipeOut#(CDPair) pin, PipeOut#(DX_t) pout);

   // Multiple in first stage
   let multStage <- mkFn_to_Pipe_Buffered (True, complex_partialProducts, True, pin );

   // Truncate result -- drop fractional bits
   // For timing this can be made a separate stage or moved into the mult stage
   PipeOut#(Vector#(4, DXFP_prod_t))  truncateRes <- mkFn_to_Pipe (map (fxptTruncateRoundSat(rndMode, satMode)), multStage);

   // Expand the result to avoid accumulation overflow/underflow
   PipeOut#(Vector#(4, DXFP_t))       extendRes   <- mkFn_to_Pipe (map (fxptSignExtend), truncateRes);

   let addStage  <- mkFn_to_Pipe_Buffered (False, complex_partialProductsAdd(satMode), True, extendRes );
   return addStage;
endmodule


// Combine the above element into a full pipe
module [Module] mkDFTPipe (PipeOut#(VData_t) vin, PipeOut#(VData_t) pout);
   // Copy the data set N  time
   let             vcopy   <- mkDataSetCopy(vin);
   let             coef    <- mkCoefPerm;
   // Merge the C and V streams into a tuple
   PipeOut#(VCDPair)  zipper <- mkJoin (zip, coef, vcopy);

   // Funnel down to (CMULT_COPIES)
   PipeOut#(Vector#(CMULT_COPIES, CDPair)) funnel <- mkFunnel(zipper);
   // Multiply data set with each permuntation
   PipeOut#(Vector#(CMULT_COPIES, DX_t)) products <- mkMap( mkMULTPIPE, funnel);

    if (doTap) begin
       products <- mkTap( showProds( "Products"), products);
    end

   // A pipelined Tree reduction
   // No saturation here since results are extended.
   PipeOut#(DX_t)            adderTree  <- mkTreeReduceFn(satPlus(Sat_Wrap) ,id, adderTreePipePlacement, products);

   // Accululate the results
   Integer productLatency =  valueOf( NPoints)/ valueOf(CMULT_COPIES);
   PipeOut#(DX_t) accum  <- mkForFold(
                                      UInt#(7) '(fromInteger(productLatency))
                                      ,mkFn_to_Pipe(uncurry(satPlus(Sat_Wrap))) // No overflow with Extended data
                                      ,adderTree);
   // Round and truncate the result to the final size
   PipeOut#(Data_t) accumT   <- mkFn_to_Pipe( cmplxMap(fxptTruncateRoundSat(rndMode, satMode)), accum );
    if (doTap) begin
       accumT <- mkTap( showC( "SUM"), accumT);
    end


   // Back to a vector and then regroup to Vector N
   PipeOut#(Vector#(1,Data_t))          vadder  <- mkFn_to_Pipe( replicate, accumT); // replicate 1 time
   PipeOut#(VData_t) regroup <- mkUnfunnel(False, vadder);
   return regroup;
endmodule

//////////////////////////////////////////////////////////////////////////
// First model for DFT
(*synthesize*)
module mkDFT_v2 (Server#(VData_t, VData_t) );
    // Convert the Pipe to a server
   let server <- mkPipe_to_Server (mkDFTPipe);
   return server;
endmodule

function Action showProds (String msg
                           ,Vector# (n, Complex#( FixedPoint #(i,f))) vin)
   provisos( Add #(TAdd#(i,f), x, 32));

   return
   (action
       fxptWriteString (msg);
       //fxptWriteNewLine;
       writePoints(vin);
    endaction);
endfunction

function Action showC (String msg
                       ,Complex#( FixedPoint #(i,f)) din)
   provisos( Add #(TAdd#(i,f), x, 32));

   return
   (action
       fxptWriteString (msg);
       // fxptWriteNewLine;
       writeCmplx(din);
    endaction);
endfunction

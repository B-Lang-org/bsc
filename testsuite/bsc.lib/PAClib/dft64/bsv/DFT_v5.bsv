

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

   // Multiple in first stage using a retimed pipeline module.   The retimed module adds extra register
   // stage which the synthesis tool can move over the containing function.
   // Number of stage is controlled by mult_pl_stages
   let multStage <- mkRetimedPipelineFn(complex_partialProducts, mult_pl_stages, pin);

   // Truncate result -- drop fractional bits
   // Again do this in a retimed stage.
   PipeOut#(Vector#(4, DXFP_prod_t))  truncateRes <- mkRetimedPipelineFn (map (fxptTruncateRoundSat(rndMode, satMode)), mult_trunc_stages, multStage);

   // Expand the result on the integer size to avoid accumulation overflow/underflow
   // and then complete the sum of the partial products
   PipeOut#(Vector#(4, DXFP_t))       extendRes   <- mkFn_to_Pipe (map (fxptSignExtend),                truncateRes);
   PipeOut#(DX_t)                    addPP        <- mkFn_to_Pipe (complex_partialProductsAdd(satMode), extendRes);

   // Use a 2 stage FIFO here to break control flow paths
   let addStage <- mkBuffer_n(2,addPP);
   return addStage;
endmodule


// Combine the above element into a full pipe
module [Module] mkDFTPipe (PipeOut#(VData_t) vin, PipeOut#(VData_t) pout);
   // Copy the data set N  time
   let             vcopy   <- mkDataSetCopy(vin);
   let             coef    <- mkCoefPerm;
   if (pipe_after_coef) begin
      coef <- mkBuffer(coef);
   end
   // Merge the C and V streams into a tuple
   PipeOut#(VCDPair)  zipper <- mkJoin (zip, coef, vcopy);

   // Funnel down to (CMULT_COPIES)
   PipeOut#(Vector#(CMULT_COPIES, CDPair)) funnel <- mkFunnel(zipper);
   if (pipe_after_funnel) begin
      funnel <- mkBuffer_n(2, funnel);
   end

   // Multiply data set with each permuntation
   PipeOut#(Vector#(CMULT_COPIES, DX_t)) products <- mkMap( mkCMultPipeline, funnel);

    if (doTap) begin
       products <- mkTap( showProds( "Products"), products);
    end

   // A pipelined Tree reduction
   // No saturation here since results are extended.
   PipeOut#(DX_t)            adderTree  <- mkTreeReduceFn(satPlus(Sat_Wrap) ,id, adderTreePipePlacement, products);
   if (pipe_after_adder_tree) begin
      adderTree <- mkBuffer_n(2, adderTree);
   end

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
module [Module] mkDFT_v5 (Server#(VData_t, VData_t) );
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

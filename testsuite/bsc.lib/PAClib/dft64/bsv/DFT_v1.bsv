

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


// Vector multiplication
// Another utility function to help  PAClib's mkMap_fn_with_funnel_indexed
function DX_t comb_mult_idx (Tuple2# (CDPair, _a) din);
   match {.x, .unused} = din;
   match {.c, .d} = x ;
   return mult_dft(satMode, c,d);
endfunction

// Use mkMap_fn_with_funnel to do the vector multiple
module [Module] mkVMultiplier (PipeOut#(VCoef_t) coefin, PipeOut#(VData_t) vin, PipeOut#(VDX_t) pout);

   // Merge the C and V streams into a tuple
   PipeOut#(VCDPair)  zipper <- mkJoin (zip,
                                        coefin,
                                        vin);
   // mkMap_fn is can configure processing into a smaller numnber of CMULT units.
   // All plumbing and book-keeping are part of this module
   PipeOut#(VDX_t) fun <- mkMap_fn_with_funnel_indexed (
                                            UInt#(CMULT_COPIES)' (?)
                                            ,comb_mult_idx
                                            ,False
                                            ,zipper);
   return fun;
endmodule

// A module, Pipe, to reduce a vector to a single element by folding over a function.
// first pass implementation is a simple combinational tree
module [Module] mkTreeReduceFn #(Bool param_buf_before
                                 ,function t reduce (t x, t y)
                                 ,Bool param_buf_after
                                 ,PipeOut#( Vector#( NPoints, t)) pin
                                 ) (PipeOut#(t))
   provisos( Bits#(t,_st) );
   PipeOut#(t) pout <- mkFn_to_Pipe_Buffered( param_buf_before
                                             ,fold(reduce)
                                             ,param_buf_after
                                             ,pin);
   return pout;
endmodule

module [Module] mkElementToVector (PipeOut#(a) pin, PipeOut# (Vector#(1, a)) pout)  ;
   function Vector#(1,a) toVector(a e);
      return cons(e,nil);
   endfunction
   // let pout <- mkFn_to_Pipe( flip(cons)(nil), pin); // Using high-order functions
   let pout <- mkFn_to_Pipe( toVector, pin);
   return pout;
endmodule

// Combine the above element into a full pipe
module [Module] mkDFTPipe (PipeOut#(VData_t) vin, PipeOut#(VData_t) pout);
   // Copy the data set N  time
   let             vcopy   <- mkDataSetCopy(vin);
   let             coef    <- mkCoefPerm;
   // Multiply data set with each permuntation
   let             mult  <- mkVMultiplier(coef, vcopy);
   // Add a buffer (may not be needed)
   let             bmult   <- mkBuffer(mult);

   // Add tree -- convert to extended precision type,  Add and then truncate.
   PipeOut#(VDX_t) multx <- mkFn_to_Pipe( map (cmplxMap(fxptSignExtend)), bmult );
   if (doTap) begin
      multx <- mkTap( showProds( "Products"), multx);
   end
   let             adderx  <- mkTreeReduceFn(True, \+ , False, multx);
   let             adder   <- mkFn_to_Pipe( cmplxMap(fxptTruncateRoundSat(rndMode, satMode)), adderx );

   // Convert element to Vector#(1), and then regroup to Vector#(N)
   let             vadder  <- mkElementToVector(adder);
   PipeOut#(VData_t) regroup <- mkUnfunnel(False, vadder);
   return regroup;
endmodule

//////////////////////////////////////////////////////////////////////////
// First model for DFT
// Use one-element input and output fifos.
// Do all complex multiplication in parallel -- using N*N-copies as the mult_dft function
(*synthesize*)
module mkDFT_v1 (Server#(VData_t, VData_t) );
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
       fxptWriteNewLine;
       writePoints(vin);
    endaction);
endfunction

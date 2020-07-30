package DFT;

//import PAClib::*;
import Complex::*;
import Vector::*;
import FixedPoint::*;
import ClientServer :: *;
import GetPut::*;
import FIFOF::*;
import Utils::*;

import DFTCoef::*;

//////////////////////////////////////////////////////////
// Configurations
// Number of points in data set -- keep small for initial testing
typedef 64             NPoints;
// Number of copies of complex multipliers used in _v1
typedef 4             CMULT_COPIES;

// Set multiplier module to use
Bool usePipelinedMult = True;   // NOT used in _v5

// Control for pipeline placement
Integer             mult_pl_stages = 4;
Integer             mult_trunc_stages = 2;
Bool                pipe_after_coef = True;
Bool                pipe_after_funnel = True;
Bool                pipe_after_adder_tree = False;
// Define a pattern for register placement in the adder tree;
Bit#(32) adderTreePipePlacement = //'hAAAA_AAAA;      // Every other step...
                                 'hFFFF_FFFF;      // Every step

// Set to True to dump result of multiplications....
Bool doTap = False;

//   Define common types for use  The Coefficients and Data use
//   differently size types although both are 10 bit wide.

typedef FixedPoint#(1,15)              CoefFP_t;
typedef FixedPoint#(6,10)             DataFP_t;
typedef FixedPoint#(6,10)             DXFP_prod_t;  // Result of partial products  truncate from full product
typedef FixedPoint#(6,10)             DXFP_t;  // Extended precision for additions tree



typedef Complex#(CoefFP_t)           Coef_t;
typedef Vector#(NPoints, Coef_t)     VCoef_t;

typedef Complex#(DataFP_t)           Data_t;
typedef Vector#(NPoints,Data_t)      VData_t;

typedef Complex#(DXFP_t)             DX_t;
typedef Vector#(NPoints,DX_t)        VDX_t;

typedef Tuple2# (Coef_t, Data_t)     CDPair;
typedef Vector# (NPoints, CDPair)    VCDPair;

RoundMode      rndMode = Rnd_Zero;
SaturationMode satMode = Sat_Bound;

// Complete the conversion of coefficient data from Real the Coef_t type.
VCoef_t coef_src = map (cmplxMap(fromReal), dftCoef_N);

/////////////////////////////////////////////////////////////////////////
// utility function to multiple Coef_t and Data_t types
// Multiplies and then resizes the result down.
function  Complex#(DXFP_prod_t) mult_dft (SaturationMode smode,
                         Coef_t x, Data_t c);
   let full = c_fxptMult(smode, x, c);
   return cmplxMap (fxptTruncateRoundSat(rndMode, satMode), full);
endfunction

//////////////////////////////////////////////////////////////////////////
// Function to generate a Vector of Vector of for coef permutations
function Vector# (n, Vector#(n, t)) genCoefPerm (Vector#(n, t) vin);
   Integer nint = valueOf(n);
   function t genCoef_k_n (Integer k, Integer n);
      return select(vin, k*n % nint);
   endfunction
   function Vector#(n, t) genCoef_k (Integer k);
      return genWith (genCoef_k_n(k));
   endfunction
   return genWith(genCoef_k);
endfunction

function Vector# (n, Vector#(n, t)) genCoefPerm_Alt (Vector#(n, t) vin);
   Integer nint = valueOf(n);
   Integer n, k;
   Vector# (n, Vector#(n, t)) res = ?;
   for (k=0; k < nint; k = k + 1) begin
      for (n=0; n < nint ; n = n + 1) begin
         res[k][n] = select(vin, k*n % nint);
         end
   end
   return res;
endfunction




endpackage

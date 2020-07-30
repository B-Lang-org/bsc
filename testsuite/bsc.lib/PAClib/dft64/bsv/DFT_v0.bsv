

//import PAClib::*;
import Complex::*;
import Vector::*;
import FixedPoint::*;
import ClientServer :: *;
import GetPut::*;
import FIFOF::*;
import Utils::*;

import DFTCoef::*;
import DFT::*;


// Combination DFT function
function VData_t dft_comb_v0 (VCoef_t coef, VData_t vin);

   Integer nint = valueOf(NPoints);
   Integer n, k;
   VData_t res;
   for (k=0; k < nint; k = k + 1) begin
      res[k] = 0;
      for (n=0; n < nint ; n = n + 1) begin
         //res[k] = res[k] + select(coef_src, k*n % nint) * idata[n];
         res[k] =  c_fxptAddSat(Sat_Bound, res[k],   mult_dft(satMode, select(coef_src, k*n % nint), vin[n]));
      end
   end
   return res;
endfunction

// Combination DFT function, using high-level programming constructs
// This version is more efficient than the above
// Used n*n complex multipliers!
function VData_t dft_comb_v1 (VCoef_t coef, VData_t vin);

   let vvcoef = genCoefPerm_Alt (coef);
   function Data_t gen_dft_k (Integer k);
      let prods = zipWith (mult_dft(satMode), select(vvcoef, k), vin);
      VDX_t xprods = map( cmplxMap(fxptSignExtend), prods);
      DX_t sum = fold(c_fxptAddSat(Sat_Bound), xprods);
      return cmplxMap(fxptTruncateRoundSat(Rnd_Zero, Sat_Bound), sum);
   endfunction

   return genWith (gen_dft_k);

endfunction

//////////////////////////////////////////////////////////////////////////
// First model for DFT
// Use one-element input and output fifos.
// Do all complex multiplication in parallel -- using N*N-copies as the mult_dft function
(*synthesize*)
module mkDFT_v0 (Server#(VData_t, VData_t) );

   // Input and output fifos
   FIFOF#(VData_t) infifo <- mkLFIFOF;
   FIFOF#(VData_t) outfifo <- mkLFIFOF;

   // Process data from infifo to outfifo
   rule process;
      infifo.deq;
      VData_t idata = infifo.first;
      let res = dft_comb_v1(coef_src, infifo.first);
      outfifo.enq(res);
   endrule

   interface request = toPut(infifo);
   interface response = toGet(outfifo);
endmodule

// Small package to provide DFT coefficients either by a direct table,
// or via generation during Bluespec static elaboration.

import Vector ::*;
import Complex:: *;
import Real::*;

// Note that these coefficients can be calculated directly during BSV
// static elaboration, see below.
Real coef_r[128] = {
		1.000000, -0.000000,
		0.995185, -0.098017,
		0.980785, -0.195090,
		0.956940, -0.290285,
		0.923880, -0.382683,
		0.881921, -0.471397,
		0.831470, -0.555570,
		0.773010, -0.634393,
		0.707107, -0.707107,
		0.634393, -0.773010,
		0.555570, -0.831470,
		0.471397, -0.881921,
		0.382683, -0.923880,
		0.290285, -0.956940,
		0.195090, -0.980785,
		0.098017, -0.995185,
		0.000000, -1.000000,
		-0.098017, -0.995185,
		-0.195090, -0.980785,
		-0.290285, -0.956940,
		-0.382683, -0.923880,
		-0.471397, -0.881921,
		-0.555570, -0.831470,
		-0.634393, -0.773010,
		-0.707107, -0.707107,
		-0.773010, -0.634393,
		-0.831470, -0.555570,
		-0.881921, -0.471397,
		-0.923880, -0.382683,
		-0.956940, -0.290285,
		-0.980785, -0.195090,
		-0.995185, -0.098017,
		-1.000000, -0.000000,
		-0.995185, 0.098017,
		-0.980785, 0.195090,
		-0.956940, 0.290285,
		-0.923880, 0.382683,
		-0.881921, 0.471397,
		-0.831470, 0.555570,
		-0.773010, 0.634393,
		-0.707107, 0.707107,
		-0.634393, 0.773010,
		-0.555570, 0.831470,
		-0.471397, 0.881921,
		-0.382683, 0.923880,
		-0.290285, 0.956940,
		-0.195090, 0.980785,
		-0.098017, 0.995185,
		-0.000000, 1.000000,
		0.098017, 0.995185,
		0.195090, 0.980785,
		0.290285, 0.956940,
		0.382683, 0.923880,
		0.471397, 0.881921,
		0.555570, 0.831470,
		0.634393, 0.773010,
		0.707107, 0.707107,
		0.773010, 0.634393,
		0.831470, 0.555570,
		0.881921, 0.471397,
		0.923880, 0.382683,
		0.956940, 0.290285,
		0.980785, 0.195090,
		0.995185, 0.098017
    };

// Take the Vector of complex and join the pair to a vector of complex
Vector#(128,Real) coef_vr = arrayToVector (coef_r);
Vector#(64,Complex#(Real)) dftCoef_vcr = mapPairs (cmplx
                                                   ,error("Odd sized vector to complex")
                                                   ,coef_vr );


// Generate a vector of Complex# (Real) representing points around the
// unit circle
function Vector#(n,Complex#(Real)) dftCoef_N ();
   function Complex#(Real) genc (Real r);
      return cmplx (cos(r), - sin(r));
   endfunction
   function Real genr (Integer i);
      Integer nint = valueOf(n);
      return (2 * pi * fromInteger(i)/fromInteger(nint));
   endfunction
   Vector#(n, Real) rs = genWith (genr);
   return map (genc, rs);
endfunction

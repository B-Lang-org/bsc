package FIRMain;

import Vector::*;

/*********************    FIR Filter Interfaces   *****************************/
/*                                                                            */
/*  This file defines interfaces for the FIR filter to use.                   */
/*                                                                            */
/*  Methods are provided to set the coefficients, input data, and get output. */
/*  Coefficients are passed as a Vector.                                       */
/*  Latency is dependent on the # of coefficients.                            */
/*                                                                            */
/******************************************************************************/

//Interface to the outside world.

interface FIRFilter#(parameter type a, parameter type n);
  method Action setCoefs(Vector#(n, a) ks);
  method ActionValue#(Maybe#(a)) fir(a data);
endinterface: FIRFilter

//Internal interfaces follow.

interface FIRHead#(parameter type a);
  method Action setCoef(a k);
  method ActionValue#(Tuple2#(a, a)) fir(a data);
endinterface: FIRHead

interface FIRBody#(parameter type a);
  method Action setCoef(a k);
  method ActionValue#(Tuple2#(a, a)) fir(a data, a r);
endinterface: FIRBody

interface FIRTail#(parameter type a);
  method Action setCoef(a k);
  method ActionValue#(a) fir(a data, a r);
endinterface: FIRTail

endpackage: FIRMain

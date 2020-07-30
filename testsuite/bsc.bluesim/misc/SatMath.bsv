// Routines for doing addition which saturates at some small value.

import Vector::*;

// This function assumes that x and y are both less than or equal to max.
function UInt#(n) addSat(UInt#(n) max, UInt#(n) x, UInt#(n) y);
   return (x > (max - y)) ? max : (x + y);
endfunction: addSat

function UInt#(n) boolToSat(Bool x);
   return x ? 1 : 0;
endfunction: boolToSat

function UInt#(n) bitToSat(Bit#(1) x);
   return (x == 0) ? 0 : 1;
endfunction: bitToSat

// Convert some bitifiable value to a vector of Bools
function Vector#(n,Bool) bitsToVector(t x) provisos(Bits#(t,n));   
   let bs = pack(x);
   Vector#(n,Bool) v = newVector;
   for (Integer i = 0; i < valueOf(n); i = i + 1)
      v[i] = (bs[i] == 1);
   return v;
endfunction: bitsToVector

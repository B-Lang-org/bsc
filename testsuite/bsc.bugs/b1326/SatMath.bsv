// Routines for doing addition which saturates at some small value.

import Vector::*;

function UInt#(n) addSat(UInt#(n) max, UInt#(n) x, UInt#(n) y);
   return (x > (max - y)) ? max : (x + y);
endfunction: addSat

function UInt#(n) boolToSat(Bool x);
   return x ? 0 : 1;
endfunction: boolToSat

function UInt#(n) bitToSat(Bit#(1) x);
   return (x == 0) ? 0 : 1;
endfunction: bitToSat

function Vector#(SizeOf#(t),Bool) bitsToVector(t x)
   provisos(Bits#(t,SizeOf#(t)));   
   let bs = pack(x);
   Vector#(SizeOf#(t),Bool) v = newVector;
   for (Integer i = 0; i < valueOf(SizeOf#(t)); i = i + 1)
      v[i] = (bs[i] == 1);
   return v;
endfunction: bitsToVector
import Vector::*;

// Div#(x,32,n) should imply Add#(x,_,TMul#(32,n))

function Vector#(n, Bit#(32)) fn(Bit#(x) v)
 provisos(Div#(x,32,n));
   return unpack(zeroExtend(v));
endfunction

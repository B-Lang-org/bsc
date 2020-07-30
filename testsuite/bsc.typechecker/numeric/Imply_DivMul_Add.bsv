// If you divide N by M, then multiply the result by M,
// you get back N or greater (due to our rounding convention).

import Vector::*;

// Here, M is 8
function Bool fn(Bit#(n) x)
provisos (Div#(n, 8, numbytes), Mul#(numbytes, 8, tot));
   Vector#(numbytes, Bit#(8)) bs = replicate(0);
   Bit#(tot) y = pack(bs);
   return (zeroExtend(x) == y);
endfunction


// Add#(_,m,32) should not be necessary

function Bool fn(Bit#(n) x, Bit#(m) y, Bit#(m) z)
 provisos (Add#(j,n,32), Add#(k,m,n));

   Bit#(32) v1 = zeroExtend(x);
   Bit#(n) v2 = zeroExtend(y);
   Bit#(32) v3 = zeroExtend(z);
   return ((v1 & v3) == zeroExtend(v2));

endfunction


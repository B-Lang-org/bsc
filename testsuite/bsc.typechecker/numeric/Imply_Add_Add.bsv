// Add#(1,_,n) should not be necessary

function Bit#(n) fn(Bit#(2) v)
 provisos (Add#(2,k,n));

   Bit#(n) v1 = zeroExtend(v);
   Bit#(n) v2 = zeroExtend(1'b1);
   return (v1 | v2);

endfunction


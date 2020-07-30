// Add#(x,_,m) and Add#(y,_,m) should not be necessary

function Bit#(m) fn(Bit#(x) v1, Bit#(y) v2)
 provisos (Max#(x,y,m));

   Bit#(m) r1 = zeroExtend(v1);
   Bit#(m) r2 = zeroExtend(v2);
   return (r1 | r2);

endfunction


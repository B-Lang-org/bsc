// Add#(x,x,n) should not be necessary

function Bit#(n) fn(Bit#(x) v)
 provisos (Mul#(x, 2, n));

   return {v, v};

endfunction


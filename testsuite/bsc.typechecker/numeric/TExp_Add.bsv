// Add#(_, n, TExp#(n)) should not be necessary

function Bool fn(Bit#(n) v1, Bit#(n) v2);
   Bit#(TExp#(n)) r1 = zeroExtend(v1);
   Bit#(TExp#(n)) r2 = zeroExtend(v2);
   return ((r1 ^ r2) == 0);
endfunction


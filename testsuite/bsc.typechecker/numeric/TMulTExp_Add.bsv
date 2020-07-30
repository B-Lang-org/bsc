// Add#(_, n, TMul#(TExp#(n), 8)) should not be necessary

function Bool fn(Bit#(n) v1, Bit#(n) v2);
   Bit#(TMul#(TExp#(n),8)) r1 = zeroExtend(v1);
   Bit#(TMul#(TExp#(n),8)) r2 = zeroExtend(v2);
   return ((r1 ^ r2) == 0);
endfunction


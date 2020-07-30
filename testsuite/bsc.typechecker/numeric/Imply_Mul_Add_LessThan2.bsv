// Add#(n, n, TMul#(2, n)) should not be necessary

function Bit#(n) fn();
   Bit#(TMul#(2, n)) m = 0;

   return truncate(m);

endfunction


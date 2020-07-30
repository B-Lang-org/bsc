// Add#(a__, n, m) should not be necessary

function Bit#(n) fn()
   provisos (Mul#(2, n, m));

   Bit#(m) z = 0;

   return truncate(z);

endfunction


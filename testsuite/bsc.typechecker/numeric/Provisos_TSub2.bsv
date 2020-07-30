function Bool fn1(Bit#(n) x) provisos (Add#( TSub#(3,n), 1, TSub#(4,n) ));
   return ?;
endfunction

// This should require "n <= 4"
function Bool fn(Bit#(n) x);
   return fn1(x);
endfunction


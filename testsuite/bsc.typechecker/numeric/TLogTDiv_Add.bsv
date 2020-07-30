// Add#(_, TLog#(TDiv#(n,32)), TLog#(n)) should not be necessary

function Bool fn(Bit#(n) v1, Bit#(n) v2);
   Bit#(TLog#(TDiv#(n,32))) r1 = 0;
   Bit#(TLog#(n)) r2 = 0;
   return (zeroExtend(r1) == r2);
endfunction


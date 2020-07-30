// Add#(_,1,TDiv#(n,m)) should not be necessary

// Not a realistic function, but it comnstructs the provisos that we want

function Bool fn(Bit#(n) x, Bit#(m) y)
 provisos (Add#(j,1,n), Add#(k,1,m));

   Bit#(1) b = 1;
   Bit#(TDiv#(n,m)) v1 = zeroExtend(b);
   return (v1 == 1);

endfunction


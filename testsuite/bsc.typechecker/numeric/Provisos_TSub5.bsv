function Bool fn(Bit#(n) x);
   Bit#(TSub#(n,8)) v1 = 0;
   Bit#(8) v2 = 0;
   Bit#(n) v3 = { v1, v2 };
   return (v3 == x);
endfunction


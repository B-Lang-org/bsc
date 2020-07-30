function Bit#(n) f1 (Bit#(n) x);
   return (x << 1);
endfunction

function Bit#(n) f2 (Bit#(n) x);
   return (x << 2);
endfunction

function Bit#(n) f4 (Bit#(n) x);
   return (x << 4);
endfunction

function Bit#(n) f (Bit#(3) s, Bit#(n) x);
   Bit#(n) x0 = (s[0] == 0) ? x  : f1(x)  ;
   Bit#(n) x1 = (s[1] == 0) ? x0 : f2(x0) ;
   Bit#(n) x2 = (s[2] == 0) ? x1 : f4(x1) ;
   return (x2);
endfunction

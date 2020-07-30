function Bit#(n) f0 (Bit#(n) x);
   return (x << 0);
endfunction

function Bit#(n) f1 (Bit#(n) x);
   return (x << 1);
endfunction

function Bit#(n) f2 (Bit#(n) x);
   return (x << 2);
endfunction

function Bit#(n) f3 (Bit#(n) x);
   return (x << 3);
endfunction

function Bit#(n) f4 (Bit#(n) x);
   return (x << 4);
endfunction

function Bit#(n) f5 (Bit#(n) x);
   return (x << 5);
endfunction

function Bit#(n) f6 (Bit#(n) x);
   return (x << 6);
endfunction

function Bit#(n) f7 (Bit#(n) x);
   return (x << 7);
endfunction

function Bit#(n) f (Bit#(3) s, Bit#(n) x);
   case (s)
      0: return f0(x);
      1: return f1(x);
      2: return f2(x);
      3: return f3(x);
      4: return f4(x);
      5: return f5(x);
      6: return f6(x);
      7: return f7(x);
   endcase
endfunction


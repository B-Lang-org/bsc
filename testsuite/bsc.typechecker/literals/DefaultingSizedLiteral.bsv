function Bool f();
    return (4'b1111 > 4'b1000);
endfunction

function Bit#(32) f2(Bit#(8) n);
   let mask = 32'b1 << ({1'b0, n} + 1);
   return mask;
endfunction


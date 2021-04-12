typedef 32 DataWidth;

function Bool is64 (Bit#(8) x);
   return (DataWidth == 64);
endfunction

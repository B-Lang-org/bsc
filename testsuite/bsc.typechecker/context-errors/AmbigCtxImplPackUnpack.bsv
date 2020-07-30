Bit#(8) y = 0;

function Bool z ();
   let v = pack( unpack(y) );
   return (v == y);
endfunction

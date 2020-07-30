Bit#(8) y = 0;

function Bool z ();
   let v = truncate( zeroExtend (y) );
   return (v == y);
endfunction

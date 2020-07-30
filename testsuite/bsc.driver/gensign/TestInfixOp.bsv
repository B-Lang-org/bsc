import InfixOp::*;

function Bit#(8) val();
   // XXX It's not really infix, if you have to call it like this
   return \~~ (1, 2);
endfunction


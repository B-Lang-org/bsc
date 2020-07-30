
// Typechecking should report that a proviso is missing in the declaration
// of "z", and should not allow this to typecheck.

function bit f( Bit#(a) x, Bit#(b) y )
//   provisos( Add#(a, b, c) )
   ;

   Bit#(c) z = {x, y};
   return (|z);
endfunction


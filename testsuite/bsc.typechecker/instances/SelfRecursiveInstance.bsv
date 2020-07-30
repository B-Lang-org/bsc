
typeclass MyEq#(type t);
    function Bool isEq(t x1, t x2);
    function Bool isNEq(t x1, t x2);
endtypeclass

instance MyEq#(Bit#(1));
    function isEq(x1, x2) = (x1 == x2);
    function isNEq(x1, x2) = (x1 != x2);
endinstance

instance MyEq#(Bit#(n))
  // this is required (include a test for it)
  provisos (MyEq#(Bit#(n)));
    function isEq(x1, x2) = (x1 == x2);
    function isNEq(x1, x2) = !isEq(x1,x2);
endinstance

// This internal errors, when the instance has the proviso
function Bool is_neq(Bit#(16) v1, Bit#(16) v2);
   return isNEq(v1, v2);
endfunction


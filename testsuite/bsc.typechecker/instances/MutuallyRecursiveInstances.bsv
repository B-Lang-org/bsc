
// two typeclasses, with instances that use each other

typeclass IsEven#(type t) provisos (Arith#(t));
    function Bool isEven(t x);
endtypeclass

typeclass IsOdd#(type t) provisos (Arith#(t));
    function Bool isOdd(t x);
endtypeclass


instance IsEven#(Bit#(1));
    function isEven(x) = (x==0);
endinstance

instance IsOdd#(Bit#(1));
    function isOdd(x) = (x==1);
endinstance


instance IsEven#(Bit#(n))
  // this is required
  provisos (IsOdd#(Bit#(n)));
    function isEven(x) = ( (x==0) ? True : isOdd(x-1) );
endinstance

instance IsOdd#(Bit#(n))
  // this is required
  provisos (IsEven#(Bit#(n)));
    function isOdd(x) = isEven(x-1);
endinstance

// This internal errors, when the instance has the proviso
function Bool is_odd(Bit#(16) v);
   return isOdd(v);
endfunction


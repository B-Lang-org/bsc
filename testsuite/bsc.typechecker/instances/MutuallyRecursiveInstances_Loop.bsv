
// two typeclasses, with instances that use each other

typeclass IsEven#(type t) provisos (Arith#(t));
    function Bool isEven(t x);
endtypeclass

typeclass IsOdd#(type t) provisos (Arith#(t));
    function Bool isOdd(t x);
endtypeclass

instance IsEven#(Bit#(n))
  provisos (IsOdd#(Bit#(n)));
    function isEven(x) = ( (x==0) ? True : isOdd(x-1) );
endinstance

instance IsOdd#(Bit#(n))
  provisos (IsEven#(Bit#(n)));
    // An infinite loop can occur if we forget the base case
    //function isOdd(x) = ( (x==0) ? False : isEven(x-1) );
    function isOdd(x) = isEven(x-1);
endinstance

function Bool is_odd(Bit#(16) v);
   return isOdd(v);
endfunction

(* synthesize *)
module sysMutuallyRecursiveInstances ();
   if (is_odd (42))
       messageM ("is_odd(42) FAIL");
     else
       messageM ("is_odd(42) PASS");
endmodule

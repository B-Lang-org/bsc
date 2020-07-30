
typeclass MyEq#(type t);
    function Bool isEq(t x1, t x2);
    function Bool isNEq(t x1, t x2);
endtypeclass

// this overlapping instance is needed, so that instance resolution
// of a polymorphic use won't resolve to a specific instance
//
instance MyEq#(Bit#(1));
    function isEq(x1, x2) = (x1 == x2);
    function isNEq(x1, x2) = (x1 != x2);
endinstance

// BSC requires the proviso because it cannot resolve the proviso
// for the use of "isEq".  There are overlapping instances, so
// typecheck of a top-level value definition would require a proviso.
// However, in this case, we're typechecking *inside* an instance,
// so we know that this code is only reached if instance resolution
// has picked this instance, so we should be able to use it again.
// If the other (overlapping) instance didn't exist, then the proviso
// would be resolved because there is only one choice.
//
instance MyEq#(Bit#(n)); // provisos (MyEq#(Bit#(n)))
    function isEq(x1, x2) = (x1 == x2);
    function isNEq(x1, x2) = !isEq(x1,x2);
endinstance


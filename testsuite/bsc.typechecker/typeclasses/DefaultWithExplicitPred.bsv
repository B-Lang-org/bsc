// Test that defaulting consults the explicit predicates

// Defaulting substitutes a concrete type for an ambiguous type variable
// only when that substitution resulting in resolving the predicate.
// One way to resolve is if the instance exists.  Another way to resolve
// is to match an explicit predicate (because the user is saying
// "assume that this instance exists").

// In the first two example, the reduction would fail if defaulting
// didn't consider the explicit predicates (and only defaulted when it
// matched an existing instance).

function a f1(b#(a) x) provisos(PrimSelectable#(b#(a), a));
   // An ambiguity exists because "0" has not been given an explicit type
   return x[0];
endfunction

function a f2(b#(a) x) provisos(PrimSelectable#(b#(a), a));
   // An ambiguity exists because "0" has not been given an explicit type
   return x[0];
endfunction

// This example would fail, because the "c" in the given predicate
// is ambiguous and cannot match the variable type of the literal "0"
/*
function a f3(b#(a) x) provisos(PrimSelectable#(b#(a),c,a));
   return x[0];
endfunction
*/


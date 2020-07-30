// This is a slightly contrived example, to avoid relying on the Vector
// package.  This situation can occur more simply with a Vector#(n,Bool)
// mismatch with Integer selection result -- in that case, the "n" variable
// in the vector should trigger the WeakCtx path.

function Tuple2#(t,t) f(t x);

   Tuple3#(t,t,t) src[3];

   // The element type (Tuple3) will not match the type expected by the
   // place doing the selection (Tuple2) and so we need to report a
   // mismatch.  This will not go down the CtxRed path because the
   // array and result types contains variables (the "a").
   // But even with a variable type, there's enough to report mismatch.

   // By declaring the type of the index to be Integer, we avoid the
   // AmbigCtx path and go down the WeakCtx path.
   Integer i=0;

   return src[i];
endfunction


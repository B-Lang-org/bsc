package BuildVector;

/*
 Note: this package uses another "advanced feature" of BSV (as well as
 typeclasses), which is not documented, namely partial application of
 functions.  For example, if we have a function
    function ResultType f (ArgType1 a1, ArgType2 a2);
       ...
    endfunction
 we can say
    let f2 = f(x);
 provided x is of type ArgType1.  f2 will be of type
    function ResultType f (ArgType2 a2);
 That is to say, we can supply the arguments to the original function f a few
 at a time (in the right order); the result of doing so is another function
 expecting the remaining arguments.  Of course, the remaining arguments, if
 there are more than one, can also be supplied a few at a time.  In the trade,
 functions like these are known as "curried functions", after the late
 logician Haskell B. Curry (after whom the language Haskell is also named).

 This implies, incidentally, that a function call "f(x,y)" can equally well be
 written in BSV as "(f(x))(y)"; or, since association is to the left,
 "f(x)(y)".
*/

import Vector::*;

// A typeclass used to implement a vector construction function which can take
// any number of arguments (>0).

// The type a is the type of Vector elements.  The function provided by the
// typeclass definition, buildVec_, takes the Vector constructed so far, and
// all the remaining elements.  But it is defined in curried form, taking just
// one of the remaining elements, and returning a function expecting the
// others.  The type r is the type of the resulting function (or the type of
// the final Vector, when all the elements have been absorbed).  The type n is
// the number of elements processed so far.
//
// So with 3 arguments, there would be three instance matches used for
// BuildVector:
//   one with r equal to Vector#(3,a)
//   one with r equal to function Vector#(3,a) f(a x)
//   one with r equal to function (function Vector#(3,a) f1(a x)) f2(a x)

// The typeclass definition:
typeclass BuildVector#(type a, type r, numeric type n)
   dependencies (r determines (a,n));
   function r buildVec_(Vector#(n,a) v, a x);
endtypeclass

// This is the base case (building a Vector from the final argument):
//
// Note that the Vector has been built up by consing successive elements onto
// the front, and so a final reverse is needed.
//
instance BuildVector#(a,Vector#(m,a),n) provisos(Add#(n,1,m));
   function Vector#(m,a) buildVec_(Vector#(n,a) v, a x);
      return reverse(cons(x,v));
   endfunction
endinstance

// This is the recursive case (building a vector from non-final arguments):
//
// Note: this uses partial application -- it defines the function expecting
// all the remaining arguments by applying buildVec_ just to the newly
// constructed "Vector so far"; the result of that is a function expecting
// buildVec_'s second argument (and, iteratively, any remaining ones).
//
instance BuildVector#(a,function r f(a y),n) provisos(BuildVector#(a,r,m), Add#(n,1,m));
   function function r f(a y) buildVec_(Vector#(n,a) v, a x);
      return buildVec_(cons(x,v));
   endfunction
endinstance

// This is the user-visible Vector constructor function:
function r vec(a x) provisos(BuildVector#(a,r,0));
   return buildVec_(nil,x);
endfunction

/*
// A simple testcase:
(* synthesize *)
module mkTest();
   Vector#(4,Bool)     v1 = vec(True,False,True,True);
   Vector#(2,UInt#(8)) v2 = vec(7,32);
   Vector#(3,Bool)     v3 = vec(False,True,True);
   Vector#(1,UInt#(4)) v4 = vec(3);

   Reg#(Bool) done <- mkReg(False);

   rule r (!done);
      $display("v1[0] -> %b", v1[0]);
      $display("v1[1] -> %b", v1[1]);
      $display("v1[2] -> %b", v1[2]);
      $display("v1[3] -> %b", v1[3]);
      $display("v2[0] -> %d", v2[0]);
      $display("v2[1] -> %d", v2[1]);
      $display("v3[0] -> %b", v3[0]);
      $display("v3[1] -> %b", v3[1]);
      $display("v3[2] -> %b", v3[2]);
      $display("v4[0] -> %d", v4[0]);

      done <= True;
   endrule

   rule r2 (done);
      $finish(0);
   endrule
endmodule
*/

endpackage

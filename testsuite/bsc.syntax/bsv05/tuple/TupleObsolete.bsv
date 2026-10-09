// tuple2..tuple8 from Prelude are deprecated (warning P0072), to point to
// the new tuple(...) syntax. The warning is given after name resolution, so
// it is only for the Prelude functions.

import List::*;

// Warned (6): every use of the Prelude functions tuple2..tuple8
function Tuple#(Bool, Bool) f2(Bool a, Bool b) = tuple2(a, b);
function Tuple#(Bool, Bool, Bool) f3(Bool a) = tuple3(a, a, a);
function Tuple#(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool) f8(Bool a) =
   tuple8(a, a, a, a, a, a, a, a);
function List#(Tuple#(Bool, Bool)) zipb(List#(Bool) xs, List#(Bool) ys) =
   List::zipWith(tuple2, xs, ys);
function function Tuple#(Bool, Bool) f(Bool b) pre2(Bool a) = tuple2(a);
function Tuple#(Bool, Bool) q2(Bool a) = Prelude::tuple2(a, a);

// Not warned: user-defined functions and arguments with the same names
function Bool applyCustom(function Bool tuple2(Bool x, Bool y), Bool a, Bool b);
   return tuple2(a, b);
endfunction

function Bool local3(Bool a);
   function Bool tuple3(Bool x, Bool y, Bool z) = x && y && z;
   return tuple3(a, a, a);
endfunction

// Not warned: the types Tuple2..Tuple8 (same types as Tuple#(...))
function Tuple2#(Bool, Bool) t2(Tuple8#(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool) t) =
   tuple(tpl_1(t), tpl_8(t));

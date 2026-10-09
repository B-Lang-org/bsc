// A curried call tuple2(a)(b) is a partial application of tuple2; it still
// works (with the deprecation warning for tuple2)

function Tuple#(Bool, Bool) f(Bool a, Bool b) = tuple2(a)(b);

function Bool inv(Bool b) = !b;

// (tuple(...)) applied to an argument, with the parentheses, is unchanged
function Tuple#(function Bool g(Bool x), Bool) h() = tuple(inv, True);
function Bool k() = tpl_1(h())(tpl_2(h()));

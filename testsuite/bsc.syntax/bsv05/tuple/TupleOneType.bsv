// Tuple#(t) is t, not a distinct one-element tuple type

typedef Tuple#(Bool) T1;

function Bool unwrap(T1 b) = b;
function T1 wrap(Bool b) = b;

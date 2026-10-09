// A user-defined top-level tuple3 and a user-defined type Tuple2 are not
// the Prelude ones, so they are not warned

typedef struct { a x; b y; } Tuple2#(type a, type b) deriving (Bits);

function Bool tuple3(Bool a, Bool b, Bool c) = a && b && c;

function Bool g() = tuple3(True, True, False);
function Tuple2#(Bool, Bool) h() = Tuple2 { x: True, y: False };

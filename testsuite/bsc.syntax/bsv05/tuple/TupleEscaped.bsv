typedef struct { a value; } \Tuple #(type a) deriving(Bits);

function Bit#(2) \tuple (Bool b) = b ? 2'b10 : 2'b01;

function \Tuple #(Bool) escapedType(Bool b) = \Tuple { value: b };
function Bit#(2) escapedCall() = \tuple (True);
function Bit#(2) qualifiedCall() = TupleEscaped::\tuple (True);

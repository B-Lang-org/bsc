package Helper;

// Type synonym
typedef Bit#(8) Byte;

// Data type with constructors
typedef enum {
    Red,
    Green,
    Blue
} Color deriving (Eq, Bits);

// Struct
typedef struct {
    Byte x;
    Byte y;
} Point deriving (Bits);

// Typeclass
typeclass Describable#(type t);
    function String describe(t val);
endtypeclass

// Function
function Byte addOne(Byte x);
    return x + 1;
endfunction

// Instance
instance Describable#(Byte);
    function String describe(Byte b);
        return "byte";
    endfunction
endinstance

export Byte;
export Color(..);
export Point(..);
export Describable(..);
export addOne;

endpackage

package ATFWrongArityBSV;

// Test that applying a type function to the wrong number of arguments
// produces an error.  Elem takes 1 argument but is used with 0 (T0025).

typeclass Container#(type f, type e)
  dependencies (f determines e);
    type Elem#(type f) = e;
    function e unwrap(f container);
endtypeclass

typedef struct { a val; } Wrapper#(type a);

instance Container#(Wrapper#(a), a);
    function a unwrap(Wrapper#(a) w) = w.val;
endinstance

// Error: Elem applied to too few arguments
function Elem test();
    return ?;
endfunction

endpackage

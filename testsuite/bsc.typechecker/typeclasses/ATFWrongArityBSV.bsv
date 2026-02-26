package ATFWrongArityBSV;

// Test that an ATF equation whose LHS has the wrong number of arguments
// compared to the class ATF declaration is an error.

typeclass Container#(type f);
    type Elem#(type f);
    function Elem#(f) unwrap(f container);
endtypeclass

typedef struct { a val; } Wrapper#(type a);

// Wrong: Elem is declared with 1 arg but the equation gives 2.
instance Container#(Wrapper#(a));
    type Elem#(Wrapper#(a), Integer) = a;  // too many args
    function a unwrap(Wrapper#(a) w) = w.val;
endinstance

endpackage

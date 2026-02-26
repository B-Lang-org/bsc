package ATFWrongPatternBSV;

// Test that an ATF equation whose LHS pattern doesn't match the instance
// head is an error.

typeclass Container#(type f);
    type Elem#(type f);
    function Elem#(f) unwrap(f container);
endtypeclass

typedef struct { a val; } Wrapper#(type a);
typedef struct { a val; } Box#(type a);

// Wrong: the ATF equation LHS uses Box#(a), not Wrapper#(a).
instance Container#(Wrapper#(a));
    type Elem#(Box#(a)) = a;  // should be Elem#(Wrapper#(a)) = a
    function a unwrap(Wrapper#(a) w) = w.val;
endinstance

endpackage

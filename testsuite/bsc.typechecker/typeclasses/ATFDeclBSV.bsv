package ATFDeclBSV;

// Test that an ATF declaration and equation parse correctly in BSV syntax
// and that the type equation is expanded by the typechecker.

typeclass Container#(type f);
    type Elem#(type f);
    function Elem#(f) unwrap(f container);
endtypeclass

typedef struct { a val; } Wrapper#(type a);

instance Container#(Wrapper#(a));
    type Elem#(Wrapper#(a)) = a;
    function a unwrap(Wrapper#(a) w) = w.val;
endinstance

endpackage

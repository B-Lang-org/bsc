package ATFDeclBSV;

// Test that a type function declaration and instance parse correctly in BSV
// syntax and that the type function is expanded by the typechecker.

typeclass Container#(type f, type e)
  dependencies (f determines e);
    type Elem#(type f) = e;
    function e unwrap(f container);
endtypeclass

typedef struct { a val; } Wrapper#(type a);

instance Container#(Wrapper#(a), a);
    function a unwrap(Wrapper#(a) w) = w.val;
endinstance

endpackage

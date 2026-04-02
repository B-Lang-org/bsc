package ATFDeclBSV;

// Test that a type function declaration and instance parse correctly in BSV
// syntax and that the type function is expanded by the typechecker.
// The type function Elem f = e is declared in the class with fundep f -> e.
// The instance Container (Wrapper a) a supplies a as the determined param.

typeclass Container#(type f, type e)
  dependencies (f determines e);
    type Elem#(type f) = e;
    function f wrap(e val);
    function e unwrap(f container);
endtypeclass

typedef struct { a val; } Wrapper#(type a);

instance Container#(Wrapper#(a), a);
    function Wrapper#(a) wrap(a val) = Wrapper { val: val };
    function a unwrap(Wrapper#(a) w) = w.val;
endinstance

// Monomorphic specialisation forces Elem(Wrapper#(Integer)) = Integer
function Integer unwrapW(Wrapper#(Integer) w) = unwrap(w);

// unwrapW(Wrapper { val: 42 }) returns Integer
Integer test = unwrapW(Wrapper { val: 42 });

endpackage

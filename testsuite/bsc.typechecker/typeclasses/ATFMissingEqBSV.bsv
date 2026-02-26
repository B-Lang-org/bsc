package ATFMissingEqBSV;

// Test that an instance which omits a required ATF equation is an error.

typeclass Container#(type f);
    type Elem#(type f);
    function Elem#(f) unwrap(f container);
endtypeclass

typedef struct { Integer val; } Wrapper#(type a);

// Missing: type Elem#(Wrapper#(a)) = Integer;
instance Container#(Wrapper#(a));
    function Integer unwrap(Wrapper#(a) w) = w.val;
endinstance

endpackage

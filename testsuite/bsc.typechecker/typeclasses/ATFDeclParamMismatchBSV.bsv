package ATFDeclParamMismatchBSV;

// Test that an ATF declaration whose parameter names don't match the class
// parameter names is an error (T0158).

typeclass Container#(type f);
    type Elem#(type g);  // wrong: should be 'f', not 'g'
    function Elem#(f) unwrap(f container);
endtypeclass

endpackage

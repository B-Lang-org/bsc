package ATFDeclParamMismatchBSV;

// Test that a type function declaration whose parameter names don't match the
// class parameter names is an error (T0158).

typeclass Container#(type f, type e)
  dependencies (f determines e);
    type Elem#(type g) = e;  // wrong: should be 'f', not 'g'
    function e unwrap(f container);
endtypeclass

endpackage

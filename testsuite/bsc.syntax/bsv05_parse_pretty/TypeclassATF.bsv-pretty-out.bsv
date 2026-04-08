package TypeclassATF;
typeclass Container #(type f, type e)
  dependencies (f determines e);
    type Elem#(type f) = e;
    function f wrap(e val);
    function e extract(f container);
endtypeclass

endpackage: TypeclassATF

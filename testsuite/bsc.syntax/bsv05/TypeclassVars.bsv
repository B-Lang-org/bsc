typeclass Foo#(parameter type a);
    a foo;
    int bar;
endtypeclass

instance Foo#(Bool);
    foo = ?;
    bar = 42;
endinstance

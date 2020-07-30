typeclass Foo#(parameter type a, parameter type b);
    function Bool foo(a x1, b x2);
endtypeclass

instance Foo#(Bool, Bool) provisos (Eq#(a));
    function Bool foo(Bool x1, Bool x2);
        foo = (x1 == x2);
    endfunction
endinstance

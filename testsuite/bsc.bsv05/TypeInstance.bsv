typeclass Foo#(parameter type a, parameter type b) provisos (Eq#(a));
    function Bool foo(a x1, b x2);
endtypeclass

instance Foo#(t, t) provisos (Eq#(t));
    function Bool foo(t x1, t x2);
        foo = (x1 == x2);
    endfunction
endinstance

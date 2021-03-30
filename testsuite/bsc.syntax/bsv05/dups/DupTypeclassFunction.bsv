typeclass Foo#(parameter type a, parameter type b) provisos (Eq#(a));
    function Bool foo(a x1, b x2);
    function Integer foo(b x1, a x2);
endtypeclass

typeclass Foo#(type x)
 dependencies (x determines ());
   function Bool fooFn(x x1);
endtypeclass

typeclass Bar#(type x)
 dependencies (() determines x);
   function Bool barFn(x x1);
endtypeclass

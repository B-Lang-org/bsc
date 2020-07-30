// A typeclass with a default (which is key to causing the error)
typeclass C#(type x) provisos (Eq#(x));
   function Bool cmeth(x v1, x v2);
      return (v1 == v2);
   endfunction
endtypeclass

instance C#(Bool);
endinstance


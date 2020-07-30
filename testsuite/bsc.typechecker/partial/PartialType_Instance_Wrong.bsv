typeclass TC#(type t);
   function t fn(t a, t b);
endtypeclass

instance TC#(Bool);
   function fn (int a, int b);
      return (a && b);
   endfunction
endinstance


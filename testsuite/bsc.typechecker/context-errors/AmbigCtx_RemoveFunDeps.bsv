typeclass C1#(type t, numeric type n)
dependencies(t determines n);
   function Bool fn1(t x);
endtypeclass

instance C1#(Integer, 1);
   function fn1(x) = True;
endinstance

instance C1#(String, 2);
   function fn1(x) = False;
endinstance

typeclass C2#(type t);
   function t fn2();
endtypeclass

instance C2#(Integer);
   function fn2 = 0;
endinstance

instance C2#(String);
   function fn2 = "0";
endinstance

module sysAmbigCtx_RemoveFunDeps();
   Reg#(Bool) rg <- mkRegU;

   rule r;
      rg <= fn1(fn2);
   endrule
endmodule

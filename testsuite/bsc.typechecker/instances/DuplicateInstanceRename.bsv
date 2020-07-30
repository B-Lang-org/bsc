typeclass TestDup#(type a);
   function Integer getTag(a val);
endtypeclass

instance TestDup#(Int#(n));
   function getTag = -valueOf(n);
endinstance

instance TestDup#(UInt#(n));
   function getTag = valueOf(n);
endinstance

instance TestDup#(Int#(m));
  function getTag = valueOf(m);
endinstance


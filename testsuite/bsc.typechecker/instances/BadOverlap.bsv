typeclass Cast#(type a, type b);
  function b cast (a val);
endtypeclass

instance Cast#(a, Bit#(sa)) provisos(Bits#(a,sa));
  function cast = pack;
endinstance

instance Cast#(Integer, b) provisos(Literal#(b));
  function cast = fromInteger;
endinstance

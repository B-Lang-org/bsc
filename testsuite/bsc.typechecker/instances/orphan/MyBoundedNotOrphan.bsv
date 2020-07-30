typeclass MyBounded#(type a);
  function a myMin();
  function a myMax();
endtypeclass

instance MyBounded#(a) provisos(Bounded#(a));
  function myMin = minBound;
  function myMax = maxBound;
endinstance

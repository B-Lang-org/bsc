instance Bounded#(a) provisos(Bits#(a,sa));
  function minBound = unpack(minBound);
  function maxBound = unpack(maxBound);
endinstance

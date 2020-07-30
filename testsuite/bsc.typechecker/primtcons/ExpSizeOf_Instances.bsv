
typedef struct {
  Bit#(SizeOf#(a)) f;
} S#(type a);

typedef struct {
  S#(a) g;
} T#(type a);

// The internal PrimMakeUndefined etc instances will exhibit the problem,
// but, in case the internals change, test it here explicitly too

instance Eq#(S#(a)) provisos (Eq#(Bit#(SizeOf#(a))));
  function \== (x,y) = (x.f == y.f);
endinstance

// Test that ctxreduce adds a Bits proviso on this instance
// (from expanding the SizeOf in the provisos added from instance
// matching the above instance for S)

instance Eq#(T#(a)) provisos (Eq#(S#(a)));
  function \== (x,y) = (x.g == y.g);
endinstance


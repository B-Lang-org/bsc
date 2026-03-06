package ATFWrongPatternMultiBSV;

// Test that a multi-parameter ATF equation whose first arg doesn't match
// the instance head is an error.

typeclass MapKey#(type k);
    type Map#(type k, type v);
    function Map#(k, v) empty();
endtypeclass

typedef struct { v val; } IntMap#(type v);
typedef struct { v val; } BoolMap#(type v);

// Wrong: class binds k=Integer, so first arg of Map must be Integer.
// Using Bool instead triggers T0156.
instance MapKey#(Integer);
    type Map#(Bool, v) = IntMap#(v);  // should be Map#(Integer, v)
    function IntMap#(v) empty() = error("empty");
endinstance

endpackage

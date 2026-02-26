package ATFExtraArgNotVarBSV;

// Test that extra arguments in an ATF equation that are not type variables
// are an error (T0159).

typeclass MapKey#(type k);
    type Map#(type k, type v);
    function Map#(k, v) empty();
endtypeclass

typedef struct { v val; } IntMap#(type v);

// Wrong: second arg 'Bool' is not a type variable.
instance MapKey#(Integer);
    type Map#(Integer, Bool) = IntMap#(Bool);  // 'Bool' should be a type variable
    function IntMap#(v) empty() = error("empty");
endinstance

endpackage

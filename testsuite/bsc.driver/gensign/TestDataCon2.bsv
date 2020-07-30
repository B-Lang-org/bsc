export U;

// The test TestDataCon.bsv tests an anonymous polymorphic substruct.
// Here, we test a non-anonymous substruct.

typedef union tagged {
   S#(t) Tag;
} U#(type t) deriving (Eq);

typedef struct {
   t b1;
   t b2;
} S#(type t) deriving (Eq);


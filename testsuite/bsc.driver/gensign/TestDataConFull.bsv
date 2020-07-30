// Export the type fully
export U(..);

typedef union tagged {
   struct { t b1; t b2; } Tag;
} U#(type t) deriving (Eq);


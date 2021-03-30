typedef union tagged {
    struct { Bool f; int f; } T;
} U deriving (Bits, Eq);


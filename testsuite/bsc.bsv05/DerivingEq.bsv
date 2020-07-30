typedef union tagged {
    Bool A;
    Bool B;
} TU deriving (Eq);

typedef struct {
    Bool a;
    Bool b;
} S deriving (Eq);

typedef enum { A, B } E deriving (Eq);

function Bool cmpTU(TU x, TU y);
   return (x == y);
endfunction

function Bool cmpS(S x, S y);
   return (x == y);
endfunction

function Bool cmpE(E x, E y);
   return (x == y);
endfunction

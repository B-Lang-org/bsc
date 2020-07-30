// Ambiguous constructor (tests tiExpr on CCon0)

import List::*;

typedef union tagged {
    Bool R;
} Foo deriving (Eq);

typedef union tagged {
    Integer R;
} Bar;

function Bool listy();
  Foo xsss[2][3][5][8];
  listy = (xsss[0][2][4][6] == R (True));
endfunction


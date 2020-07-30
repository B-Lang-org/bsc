// An example where tiExpr on CCon0 can't disambiguate R because
// the return type is not sufficiently known.  Though notice that
// Foo x = R (True) *can* be disambiguated.

import List::*;

typedef union tagged {
    Bool R;
} Foo;

typedef union tagged {
    Integer R;
} Bar;

function Bool listy();
  Foo xsss[2][3][5][8];
  Foo x = R (True);
  xsss[0][2][4][6] = R (True);
  listy = True;
endfunction


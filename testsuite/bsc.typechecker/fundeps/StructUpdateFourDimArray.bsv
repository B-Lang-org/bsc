// Wow.  This gives an ambiguity, even though the type of x is given!
// This exercises the struct update handling (as in StructUpdateOneDimArray.bs)

typedef struct {
    Bool field1;
    Bool field2;
	       } Bar;

typedef struct {
    Bool field1;
    Bool field2;
	       } Foo;


function Bool listy();
  Foo xsss[2][3][5][8];
  Foo x = xsss[0][2][4][6];
  x.field1 = True;
  listy = (xsss[0][2][4][6]).field1;
endfunction


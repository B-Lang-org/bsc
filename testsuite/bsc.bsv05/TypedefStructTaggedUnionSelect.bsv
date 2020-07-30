typedef struct {
    Bool one;
    union tagged {
        Bool Foo;
        Bool Bar;
    } either;
    union tagged {
        Bool One;
        struct {
          Bool twoA;
          Bool twoB;
        } Two;
    } oneTwo;
    Bool four;
} OneTwoThreeFour;

function Bool sel(OneTwoThreeFour stuff);
  sel = stuff.either.Foo;
endfunction

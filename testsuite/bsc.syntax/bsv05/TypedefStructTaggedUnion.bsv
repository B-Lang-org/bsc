typedef struct {
    Bool one;
    union tagged {
        Bool Left;
        Bool Right;
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

typedef union tagged {
   int TagI;
   struct {
     bit foo;
     Bool bar;
   } TagOh;
} U deriving(Bits);

U x = tagged TagI 23;
U y = tagged TagOh { foo: 1, bar: False };
U z = tagged TagI (15);

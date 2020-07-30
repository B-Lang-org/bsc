typedef struct {
   Bool f1;
   Bool f2;
 } MyStruct deriving(Bits);

typedef union tagged {
   Bool T1;
   MyStruct T2;
 } MyUnion deriving(Eq, Bits);


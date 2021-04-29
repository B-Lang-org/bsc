typedef enum { E1, E2, E3 } Enum;

Enum e1 = E1;
Enum e2 = tagged E2;

typedef union tagged {
  void EL1;
  void EL2;
  void EL3;
} EnumLike;

EnumLike el1 = EL1;

EnumLike el2 = tagged EL2;

typedef union tagged {
  void MyNil;
  struct { a car; MyList#(a) cdr; } MyCons;
} MyList#(type a);

MyList#(Bool) ml1 = MyNil;

MyList#(Bool) ml2 = tagged MyNil;

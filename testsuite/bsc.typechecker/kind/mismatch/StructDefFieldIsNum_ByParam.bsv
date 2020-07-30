// This is a mix of the test ../StructDefFieldIsNum.bs (that struct fields
// have kind Star) and ../StructDefParamGivenNumUsedNonNum.bs (where the
// user has specified the kind of a type parameter, and used it as an
// argument to a constructor which is not expecting a numeric).

typedef struct {
   a f1;
} S#(numeric type a);


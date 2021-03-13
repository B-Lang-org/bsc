
typedef union tagged {
  struct {
    UInt#(8) x;
    Bool y;
    Int#(32) z;
  } C1;
  UInt#(16) C2;
  void C3;
} FooBSV  deriving (FShow, Eq);


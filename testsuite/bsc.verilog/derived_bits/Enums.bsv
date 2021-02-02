typedef enum { A, B, C, D, E, F, G, H, I } Type1 deriving (Bits, Eq);
typedef enum { A = 1, B, C, D, E, F, G, H, I } Type2 deriving (Bits, Eq);
typedef enum { A, B = 2, C, D, E = 6, F = 8, G, H = 12, I = 15 } Type3 deriving (Bits, Eq);

(* synthesize *)
module mkEnumType1Reg(Reg#(Type1));
  Reg#(Type1) r <- mkReg(H);
  return(r);
endmodule

(* synthesize *)
module mkEnumType2Reg(Reg#(Type2));
  Reg#(Type2) r <- mkReg(H);
  return(r);
endmodule

(* synthesize *)
module mkEnumType3Reg(Reg#(Type3));
  Reg#(Type3) r <- mkReg(H);
  return(r);
endmodule

interface Test;
  method Bool isA();
  method Bool isB();
  method Bool isC();
  method Bool isD();
  method Bool isE();
  method Bool isF();
  method Bool isG();
  method Bool isH();
  method Bool isI();
endinterface

(* synthesize *)
module mkEnumType1Test(Test);

  Reg#(Type1) r <- mkReg(I);

  method isA = r == A;
  method isB = r == B;
  method isC = r == C;
  method isD = r == D;
  method isE = r == E;
  method isF = r == F;
  method isG = r == G;
  method isH = r == H;
  method isI = r == I;

endmodule

(* synthesize *)
module mkEnumType2Test(Test);

  Reg#(Type2) r <- mkReg(I);

  method isA = r == A;
  method isB = r == B;
  method isC = r == C;
  method isD = r == D;
  method isE = r == E;
  method isF = r == F;
  method isG = r == G;
  method isH = r == H;
  method isI = r == I;

endmodule

(* synthesize *)
module mkEnumType3Test(Test);

  Reg#(Type3) r <- mkReg(I);

  method isA = r == A;
  method isB = r == B;
  method isC = r == C;
  method isD = r == D;
  method isE = r == E;
  method isF = r == F;
  method isG = r == G;
  method isH = r == H;
  method isI = r == I;

endmodule

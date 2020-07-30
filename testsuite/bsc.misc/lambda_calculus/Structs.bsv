import FixedPoint::*;

typedef FixedPoint#(5,4)  XXX;
typedef FixedPoint#(5,4)  ZZZ;

typedef struct {
   UInt#(4) a;
   UInt#(4) b;
   UInt#(4) c;
   } Triple
deriving(Bits);


(*synthesize*)
module sysStructs ();
   Reg#(XXX) a <- mkReg(0);
   Reg#(XXX) b <- mkReg(0.5);
   Reg#(ZZZ) c <- mkReg(0.5);
   Reg#(Bool) s <- mkReg(False);
   Reg#(Bool) s1 <- mkReg(False);
   Reg#(Bool) s2 <- mkReg(False);
   Reg#(Bool) s3 <- mkReg(False);

   Reg#(Triple) t0 <- mkRegU;
   Reg#(Triple) t1 <- mkRegU;
   Reg#(Triple) t2 <- mkRegU;

   
   rule add_em (s);
      a <= a + b + 0.25;
      s <= ! s;
   endrule

   // rule mult_em (!s);
   //    a <= a * b;
   //    s <= ! s;
   // endrule
   
   
   // rule x2 (s1 && s2 && s3);
   //    a <= negate(b);
   //    let x = 0;
   //    x.i = b.i;
   //    x.f = b.f;
   //    c <= x;
   // endrule
   
   rule tss ;
      let tx = t1;
      tx.a = t2.a;
      tx.b = t2.b;
      t2 <= tx;
   endrule
endmodule

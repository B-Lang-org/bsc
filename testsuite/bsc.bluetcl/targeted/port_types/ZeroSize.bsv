typedef struct {
  UInt#(t1) field1;
  UInt#(t2) field2;
} T#(type t1, type t2) deriving(Bits, Eq);

interface Ifc#(type t1, type t2);
   method T#(t1,t2) m1 (T#(t1,t2) val);
   method Action    m2 (T#(t1,t2) x, Bool y);
   method ActionValue#(T#(t1,t2)) m3 (Bit#(t1) x);
   interface Inout#(UInt#(t2)) i1;
endinterface

(* synthesize *)
module sysZeroSize #(Inout#(UInt#(0)) io) ();
  Reg#(T#(0,0)) rg1 <- mkZeroSize_BVI;
  Ifc#(0,0) rg2 <- mkZeroSize_Sub(0, io);
endmodule


import "BVI" MOD =
module mkZeroSize_BVI(Reg#(a) ifc)
   provisos (Bits#(a, sa)) ;

   method D_OUT _read() ;
   method _write(Q_IN) enable(EN) ;

   schedule   _read CF _read ;
   schedule   _read SB _write ;
   schedule   _write SBR _write ;
endmodule


(* synthesize *)
module mkZeroSize_Sub #(Bit#(0) p, Inout#(UInt#(0)) io) (Ifc#(0,0));
   Reg#(T#(0,0)) rg <- mkRegU;

   method m1(y) = y;
   method Action m2 (x, y);
     rg <= x;
   endmethod
   method ActionValue#(T#(0,0)) m3 (x);
     rg <= rg;
     return rg;
   endmethod
   interface i1 = io;
endmodule


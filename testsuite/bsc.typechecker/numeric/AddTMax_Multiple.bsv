typedef union tagged {
    Bit#(t1) T1;
    Bit#(t2) T2;
    Bit#(t3) T3;
    Bit#(t4) T4;
    Bit#(t5) T5;
} U#(type t1, type t2, type t3, type t4, type t5)
      deriving (Eq, Bits);

module sysTestMultipleMax (Reg#(U#(a,b,c,d,e)));
   Reg#(U#(a,b,c,d,e)) rg <- mkRegU;
   return rg;
endmodule
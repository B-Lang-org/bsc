interface Ifc#(numeric type x, numeric type y);
endinterface

// BSC should reduce the proviso requirement to NumEq(n,m)

(* synthesize *)
module sysMul_Elimination1(Ifc#(n, m));

   // These could be expressed as Vectors,
   // but no need to complicate the test case

   // 5 groups of n bytes
   Reg#(Bit#(TMul#(5,TMul#(n,8)))) rg1 <- mkRegU;
   // 5 groups of m bytes
   Reg#(Bit#(TMul#(5,TMul#(m,8)))) rg2 <- mkRegU;

   rule shift;
      rg1 <= rg2;
   endrule

endmodule


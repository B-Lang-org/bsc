import Vector::*;

interface Ifc#(type a, type b, type c);
    method Action put1(Vector#(a, Vector#(b, Bit#(c))) vec);
    method Action put2(Vector#(b, Vector#(c, Bit#(a))) vec);
    method Action put3(Vector#(c, Vector#(a, Bit#(b))) vec);
endinterface

(* synthesize *)
module sysMulTMul_Multiple (Ifc#(x,y,z));
   Reg#(Bit#(TMul#(x,TMul#(y,z)))) rg1 <- mkRegU;
   Reg#(Bit#(TMul#(TMul#(y,z),x))) rg2 <- mkRegU;
   Reg#(Bit#(TMul#(TMul#(x,z),y))) rg3 <- mkRegU;

   rule shift;
      rg1 <= rg2;
      rg2 <= rg3;
      rg3 <= rg1;
   endrule

   method Action put1(Vector#(x, Vector#(y, Bit#(z))) vec);
      rg1 <= pack(vec);
      rg2 <= pack(vec);
      rg3 <= pack(vec);
   endmethod

   method Action put2(Vector#(y, Vector#(z, Bit#(x))) vec);
      rg1 <= pack(vec);
      rg2 <= pack(vec);
      rg3 <= pack(vec);
   endmethod

   method Action put3(Vector#(z, Vector#(x, Bit#(y))) vec);
      rg1 <= pack(vec);
      rg2 <= pack(vec);
      rg3 <= pack(vec);
   endmethod
endmodule


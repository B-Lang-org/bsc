   typedef union tagged {
     a Read;
     v Write;
   } Foo#(type a,type v) deriving(Bits, Eq);

   interface Ifc#(type a, type v);
     method Foo#(a,v) m();
   endinterface

   module mkTest(Ifc#(a,v)) provisos(Bits#(a,sa), Bits#(v,sv));
      Reg#(Foo#(a,v)) rg <- mkRegU;
      method m = rg;
   endmodule


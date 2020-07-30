
interface Ifc;
   method ActionValue#(Bool) m(Bool x);
endinterface

module mkTest(Ifc);
   Reg#(Bool) rg <- mkRegU;

   method ActionValue#(int) m(x);
      rg <= x;
      return rg;
   endmethod
endmodule


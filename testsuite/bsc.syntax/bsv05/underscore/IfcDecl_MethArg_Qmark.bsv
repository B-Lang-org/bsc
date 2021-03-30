interface Ifc;
  method Action m(Bool ?);
endinterface

module sysIfcDecl_MethArg_Qmark(Ifc);
   Reg#(Bool) rg <- mkRegU;

   method Action m(Bool b);
     rg <= b;
   endmethod
endmodule


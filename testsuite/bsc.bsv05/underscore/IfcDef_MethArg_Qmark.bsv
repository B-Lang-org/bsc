interface Ifc;
  method Action m(Bool b);
endinterface

module sysIfcDef_MethArg_Qmark(Ifc);
   Reg#(Bool) rg <- mkRegU;

   method Action m(Bool ?);
     rg <= True;
   endmethod
endmodule


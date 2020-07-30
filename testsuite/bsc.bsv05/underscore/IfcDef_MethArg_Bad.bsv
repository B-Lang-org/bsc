interface Ifc;
  method Action m(Bool b);
endinterface

module sysIfcDef_MethArg_Bad(Ifc);
   Reg#(Bit#(8)) rg <- mkRegU;

   // Test that "_" has the right type by expecting a failure on mis-use
   method Action m(Bool _);
     rg <= _;
   endmethod
endmodule


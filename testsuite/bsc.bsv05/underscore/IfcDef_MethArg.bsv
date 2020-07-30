interface Ifc;
  method Action m(Bool b);
endinterface

(* synthesize *)
module sysIfcDef_MethArg(Ifc);
   Reg#(Bool) rg <- mkRegU;

   method Action m(Bool _);
     rg <= _;
   endmethod
endmodule


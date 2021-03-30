interface Ifc;
  method Action m(Bool _);
endinterface

(* synthesize *)
module sysIfcDecl_MethArg(Ifc);
   Reg#(Bool) rg <- mkRegU;

   method Action m(Bool b);
     rg <= b;
   endmethod
endmodule


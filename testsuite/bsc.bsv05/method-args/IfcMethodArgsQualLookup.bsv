import IfcMethodArgsQualLookup_Sub::*;

interface Ifc;
  method Action m1(Bool a1, Bool a2);
endinterface

(* synthesize *)
module sysIfcMethodArgsQualLookup (Ifc);
  method Action m1(Bool a1, Bool a2);
    noAction;
  endmethod
endmodule


package IFC;

interface IFC#(type anyType);
  (* prefix = "precomp_ifc" *)
 method Action start(anyType a, anyType b);
  (* prefix = "precomp_ifc" *)
 method anyType result(anyType c);
  (* prefix = "precomp_ifc" *)
 method ActionValue#(anyType) check(anyType d);
endinterface

endpackage

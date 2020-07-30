package IFC;

interface IFC#(type anyType);
(* enable = "stenable" *)
method Action start(anyType a, anyType b);
method anyType result(anyType c);
(* enable = "chenable" *) 
method ActionValue#(anyType) check(anyType d);
endinterface

endpackage

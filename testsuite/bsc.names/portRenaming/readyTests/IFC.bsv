package IFC;

interface IFC#(type anyType);
(* ready = "stready" *)
method Action start(anyType a, anyType b);
(* ready = "resready" *) 
method anyType result(anyType c);
(* ready = "chready" *) 
method ActionValue#(anyType) check(anyType d);
endinterface

endpackage

package IFC;
import S1 :: * ;

interface IFC#(type aA);
 method Action start(aA a, aA b);
 (* prefix = "sub_ifc_$" *)
 interface S1#(aA) subIFC;
endinterface

endpackage 

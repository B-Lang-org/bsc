package IFC1;
(* always_enabled *)
interface IFC#(type mType);
  method Action start(mType a, mType b);
  method mType result(mType c);
  method ActionValue#(mType) check(mType d);
endinterface

endpackage


package IFC;
interface IFC#(type mType);
 method Action start(mType a, mType b);
  (* result = "resresult" *)
 method mType result(mType c);
  (* result = "chresult" *)
 method ActionValue#(mType) check(mType d);
endinterface

	
endpackage

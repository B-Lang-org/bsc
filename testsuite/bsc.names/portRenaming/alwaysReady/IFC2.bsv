package IFC2;

interface S1#(type aA);
  method aA result(aA c);
  method ActionValue#(aA) check(aA d);
endinterface

interface IFC#(type mType);
  method Action start(mType a, mType b);
  (* always_ready *)
  interface S1#(mType) subIFC;
endinterface

endpackage


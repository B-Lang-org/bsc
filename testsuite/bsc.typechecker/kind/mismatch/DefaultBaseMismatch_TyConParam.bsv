// The type parameter defaults to Star kind
interface Ifc#(type m);
   method Bool fn(Bool x);
endinterface

module mkDefaultBaseMismatch_TyConParam (Ifc#(2));
   method fn(x) = x;
endmodule


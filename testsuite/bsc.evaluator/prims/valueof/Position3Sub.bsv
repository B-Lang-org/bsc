interface Ifc#(type t, type t2);
endinterface

module mkSub(Ifc#(t,t2))
 provisos (Bits#(t,st), Bits#(t2,st2), Literal#(t2));
   let n = valueof(st);
   Reg#(t2) rg <- mkReg(fromInteger(n));
endmodule

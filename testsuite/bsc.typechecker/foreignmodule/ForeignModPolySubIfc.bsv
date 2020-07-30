interface SubIfc#(type a);
  method ActionValue#(a) m();
endinterface

interface Ifc#(type b);
  interface SubIfc#(b) s;
endinterface

import "BVI" MOD =
module mkSubIfc ( Ifc#(c) ) provisos(Bits#(c,sc));
  interface SubIfc s;
    method Q_OUT m () enable (EN);
  endinterface
  schedule s.m C s.m;
endmodule


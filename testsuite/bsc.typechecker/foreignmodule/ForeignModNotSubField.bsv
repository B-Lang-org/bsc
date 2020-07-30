interface SubIfc;
  method ActionValue#(Bool) m();
endinterface

interface Ifc;
  interface SubIfc s;
endinterface

import "BVI" MOD =
module mkMod ( Ifc );
  interface SubIfc s;
    method Q_OUT m1 () enable (EN);
  endinterface
  schedule s.m1 C s.m1;
endmodule


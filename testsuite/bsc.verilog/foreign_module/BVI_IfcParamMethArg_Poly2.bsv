interface Ifc#(type a);
   method Bool m(a x);
endinterface

import "BVI"
module mkMod(Ifc#(Bit#(b)));
  default_clock clk();
  default_reset rst();
  method RES m(ARG);
  schedule m CF m;
endmodule


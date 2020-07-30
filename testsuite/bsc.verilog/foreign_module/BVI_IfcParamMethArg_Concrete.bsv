interface Ifc#(type a);
   method Bool m(a x);
endinterface

import "BVI"
module mkMod(Ifc#(Bit#(8)));
  default_clock clk();
  default_reset rst();
  method RES m(ARG);
  schedule m CF m;
endmodule


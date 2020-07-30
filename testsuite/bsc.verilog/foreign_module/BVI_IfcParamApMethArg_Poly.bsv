interface Ifc#(type a);
   method Bool m(a#(8) x);
endinterface

import "BVI"
module mkMod(Ifc#(b));
  default_clock clk();
  default_reset rst();
  method RES m(ARG);
  schedule m CF m;
endmodule


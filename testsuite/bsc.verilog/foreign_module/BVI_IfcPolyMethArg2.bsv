interface Ifc;
   method Bool m(a#(b) x);
endinterface

import "BVI"
module mkMod(Ifc);
  default_clock clk();
  default_reset rst();
endmodule


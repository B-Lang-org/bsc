interface IFC;
   method Action m();
endinterface

import "BVI" VMod =
  module mkMod (IFC);
     default_clock clk();
     default_reset rst();
     method foo() enable(E1);
     method m() enable(E2);
  endmodule


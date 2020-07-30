interface I;
   // value method
   method Bool vm();
   // action method
   method Action am();
   // actionvalue method
   method ActionValue#(Bool) avm();
endinterface

import "BVI" VMod =
module mkI (I);
   default_clock clk();
   default_reset rst();
   // unexpected enable
   method vm() enable(EN);
   // for completeness
   method A avm() enable(B);
   method am() enable(C);
endmodule

import "BVI" VMod =
module mkI2 (I);
   default_clock clk();
   default_reset rst();
   // unexpected enable
   method M vm() enable(EN);
   // for completeness
   method A avm() enable(B);
   method am() enable(C);
endmodule


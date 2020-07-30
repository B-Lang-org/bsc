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
   // unexpected value
   method M am() enable(EN);
   // for completeness
   method A avm() enable(B);
   method C vm();
endmodule

import "BVI" VMod =
module mkI2 (I);
   default_clock clk();
   default_reset rst();
   // unexpected value
   method M am();
   // for completeness
   method A avm() enable(B);
   method C vm();
endmodule

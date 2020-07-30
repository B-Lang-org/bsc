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
   // missing value
   method avm() enable(EN);
   // for completeness
   method A vm();
   method am() enable(B);
endmodule


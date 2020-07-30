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
   // missing enable
   method M avm();
   // for completeness
   method A vm();
   method am() enable(B);
endmodule


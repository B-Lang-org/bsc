
// Test that the ModArg and the BVI get assigned different clocks
// and that the connection fails

(*synthesize*)
module sysCheckClocks_ModArgToBVI_DiffClock
         (Clock c2,
          Inout#(int) x1,
          (*clocked_by="c2"*) Inout#(int) x2,
          Empty e);
   mkConnect(x1,x2);
endmodule


import "BVI" Connect =
module mkConnect#(Inout#(a) x1, Inout#(a) x2) (Empty)
   provisos(Bits#(a,sa));

   parameter width = valueOf(sa);
   default_clock clk();
   default_reset rst();
   inout X1 = x1;
   inout X2 = x2;
endmodule


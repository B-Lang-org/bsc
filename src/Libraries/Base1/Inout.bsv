package Inout;

import "BVI" InoutConnect =
module vInoutConnect#(Inout#(a) x1, Inout#(a) x2) (Empty)
   provisos(Bits#(a,sa));

   parameter width = valueOf(sa);

   /*
    x1 and x2 must be on the same clock, which itself may be a DIFFERENT
    clock than the parent module of the mkConnection.
    This is a somewhat arbitrarily chosen
    design decision corresponding to a degree of strictness in clock
    checking on inouts that we (stoy and ken) believe would be useful
    to a user of inouts.
   */

   default_clock clk()= clockOf(x1);
   inout X1 = x1;
   inout X2 = x2; /* x2's clock is inferred to be default_clk,
                     namely clockOf(x1).  If x2's clock is not that clock,
                     then a compilation error should result. */

   /* similarly, they must be on the same reset. */
   default_reset rst() = resetOf(x1);
endmodule: vInoutConnect

import "BVI" InoutSplit =
module inoutSplit#(Inout#(a0) x0, Inout#(a1) x1, Inout#(a2) x2) (Empty)
   provisos(Bits#(a0,sa0),Bits#(a1,sa1),Bits#(a2,sa2), Add#(sa1,sa2,sa0));

   parameter width0 = valueOf(sa0);
   parameter width1 = valueOf(sa1);
   parameter width2 = valueOf(sa2);

   /*
    All args must be on the same clock, which itself may be a DIFFERENT
    clock than the parent module.  This is a somewhat arbitrarily chosen design
    decision corresponding to a degree of strictness in clock checking on
    inouts that we (stoy and ken) believe would be useful to a user of
    inouts.
   */

   default_clock clk()= clockOf(x0);
   inout X0 = x0;
   inout X1 = x1;
   inout X2 = x2;

   /* similarly, they must be on the same reset. */
   default_reset rst() = resetOf(x0);
endmodule: inoutSplit

endpackage: Inout

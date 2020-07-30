import "BVI" Mod =
   module mkMod(Empty);
      default_clock no_clock;
      default_reset rst(RSTN) clocked_by(foo);
   endmodule


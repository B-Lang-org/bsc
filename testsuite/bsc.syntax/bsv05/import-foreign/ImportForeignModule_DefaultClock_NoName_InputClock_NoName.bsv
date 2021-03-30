import "BVI" MOD =
module mkMod () ;

   default_clock (CLK1) <- exposeCurrentClock ;
   no_reset ;

   input_clock (CLK2) <- exposeCurrentClock ;

endmodule


import "BVI" MOD =
module mkMod () ;

   default_reset (RST1) <- exposeCurrentReset ;

   input_reset (RST2) <- exposeCurrentReset ;

endmodule


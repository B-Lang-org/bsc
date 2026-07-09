// Error: the "default_reset" value names an argument which is not a Reset
// (so it cannot be a designation, and renaming the default reset port to
// the name of another argument is not supported)

(* synthesize *)
(* default_reset = "clk_in" *)
module sysDefaultResetArg_WrongType(Clock clk_in, Empty ifc);
   rule r_disp;
      $display("Hello");
   endrule
endmodule

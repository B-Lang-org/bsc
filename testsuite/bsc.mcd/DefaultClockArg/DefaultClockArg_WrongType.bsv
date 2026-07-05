// Error: the "default_clock" value names an argument which is not a Clock

(* synthesize *)
(* default_clock = "rst_in" *)
module sysDefaultClockArg_WrongType(Clock clk_in, Reset rst_in, Empty ifc);
   rule r_disp;
      $display("Hello");
   endrule
endmodule

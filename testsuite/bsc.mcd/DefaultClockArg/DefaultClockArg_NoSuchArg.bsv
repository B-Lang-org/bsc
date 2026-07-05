// Error: the "default_clock" value does not name an argument

(* synthesize *)
(* default_clock = "bogus" *)
module sysDefaultClockArg_NoSuchArg(Clock clk_in, Empty ifc);
   rule r_disp;
      $display("Hello");
   endrule
endmodule

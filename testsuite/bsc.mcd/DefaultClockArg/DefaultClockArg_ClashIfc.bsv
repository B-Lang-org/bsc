// Error: a method port conflicts with the port name given for a
// designated default clock argument

interface IfcC;
   (* result = "XCLK" *)
   method UInt#(8) count();
endinterface

(* synthesize *)
(* default_clock = "clk_in", default_clock_osc = "XCLK" *)
(* no_default_reset *)
module sysDefaultClockArg_ClashIfc(Clock clk_in, IfcC ifc);
   Reg#(UInt#(8)) ctr <- mkReg(0, reset_by noReset);

   rule r_tick;
      ctr <= ctr + 1;
   endrule

   method count = ctr;
endmodule

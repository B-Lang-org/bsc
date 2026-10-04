import Clocks::*;

// With -sva-runtime-checks, the runtime check gets one assertion for each
// oscillator of the clock domain (here, CLK and the gated clock)

(* synthesize *)
module sysMutuallyExclusiveSVAGated(Empty);
   GatedClockIfc g <- mkGatedClockFromCC(True);
   Reg#(Bit#(4)) r <- mkReg(0);
   Reg#(Bit#(4)) s <- mkReg(0, clocked_by g.new_clk);

   rule toggle_gate;
      g.setGateCond(r[1] == 0);
   endrule

   (* mutually_exclusive = "a, b" *)
   rule a (r[0] == 0);
      r <= r + 1;
   endrule

   rule b (s[0] == 0);
      r <= r + 3;
   endrule

   rule tick_s;
      s <= s + 1;
   endrule
endmodule

import "BVI"
module mkBVI#(Clock c1, Reset r1, Clock c2, Reset r2)();
   default_clock no_clock;
   default_reset no_reset;

   input_clock clk1 (CLK1) = c1;
   input_reset rst1 (RST1) clocked_by(clk1) = r1;

   input_clock clk2 (CLK2) = c2;
   input_reset rst2 (RST2) clocked_by(clk2) = r2;

   same_family(clk1,clk2);
endmodule

(* synthesize *)
(* clock_family = "default_clock, c2" *)
module sysDeriveResetClock_SubModTwoArgsSameDomain #(Clock c2, Reset r2)();
   Clock c1 <- exposeCurrentClock;

   // use r2 with two clocks in the same domain
   mkBVI(c1,r2,c2,r2);

endmodule

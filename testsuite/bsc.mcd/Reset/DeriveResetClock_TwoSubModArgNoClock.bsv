import "BVI"
module mkBVI#(Reset r)();
   default_clock no_clock;
   default_reset no_reset;
   input_reset rst (RST) clocked_by(no_clock) = r;
endmodule

(* synthesize *)
module sysDeriveResetClock_TwoSubModArgNoClock #(Reset r2)();

   mkBVI(r2);
   mkBVI(r2);

endmodule

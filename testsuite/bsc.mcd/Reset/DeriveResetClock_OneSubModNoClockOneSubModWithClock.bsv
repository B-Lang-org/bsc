import "BVI"
module mkBVI#(Reset r)();
   default_clock no_clock;
   default_reset no_reset;
   input_reset rst (RST) clocked_by(no_clock) = r;
endmodule

(* synthesize *)
module sysDeriveResetClock_OneSubModNoClockOneSubModWithClock #(Reset r2)();

   // test that this doesn't disrupt r2 for the Reg instantiation
   mkBVI(r2);

   // this is clocked by the current clock
   Reg#(Bool) rg <- mkReg(True, reset_by r2);

   // test that after the Reg instantiation this is still OK
   mkBVI(r2);

endmodule

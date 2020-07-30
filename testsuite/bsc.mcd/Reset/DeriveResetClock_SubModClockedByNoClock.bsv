(* synthesize *)
module sysDeriveResetClock_SubModClockedByNoClock #(Reset r2)();

   Reg#(Bool) rg <- mkReg(True, reset_by r2, clocked_by noClock);

endmodule

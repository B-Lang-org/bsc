import Clocks :: *;

(* synthesize *)
module sysClockedBy_DefaultClock_RightDomain
              (Clock c2,
	       (* clocked_by="default_clock" *)
	       Reset rst,
	       Empty ifc);

   Reg#(Bool) r1 <- mkReg(True, reset_by rst);

endmodule

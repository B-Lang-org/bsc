import Clocks :: *;

(* synthesize *)
module sysClockedBy_DefaultClock_WrongDomain
              (Clock c2,
	       (* clocked_by="default_clock" *)
	       Reset rst,
	       Empty ifc);

   // c2 is not in the same domain
   Reg#(Bool) r2 <- mkReg(True, reset_by rst, clocked_by c2);

endmodule

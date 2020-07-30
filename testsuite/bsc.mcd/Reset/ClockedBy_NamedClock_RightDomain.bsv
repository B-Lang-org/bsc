import Clocks :: *;

(* synthesize *)
module sysClockedBy_NamedClock_RightDomain
              (Clock c2,
	       (* clocked_by="c2" *)
	       Reset rst,
	       Empty ifc);

   Reg#(Bool) r2 <- mkReg(True, reset_by rst, clocked_by c2);

endmodule

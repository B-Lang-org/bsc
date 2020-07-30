import Clocks :: *;

(* synthesize *)
module sysClockedBy_NamedClock_WrongDomain
              (Clock c2,
	       (* clocked_by="c2" *)
	       Reset rst,
	       Empty ifc);

   Reg#(Bool) r <- mkReg(True, reset_by rst);

endmodule

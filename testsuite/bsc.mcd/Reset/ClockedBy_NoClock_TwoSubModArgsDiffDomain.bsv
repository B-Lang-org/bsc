import Clocks :: *;

(* synthesize *)
module sysClockedBy_NoClock_TwoSubModArgsDiffDomain
              (Clock c2,
	       (* clocked_by="no_clock" *)
	       Reset rst,
	       Empty ifc);

   Reg#(Bool) r1 <- mkReg(True, reset_by rst);
   // c2 is not in the same domain
   Reg#(Bool) r2 <- mkReg(True, reset_by rst, clocked_by c2);

endmodule

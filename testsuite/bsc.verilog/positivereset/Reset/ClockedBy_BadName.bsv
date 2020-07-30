import Clocks :: *;

(* synthesize *)
module sysClockedBy_BadName (Clock c2,
			     (* clocked_by="c3" *)
			     Reset rst,
			     Empty ifc);

endmodule


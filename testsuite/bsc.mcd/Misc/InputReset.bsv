(* synthesize *)
module sysInputReset(Reset rst, Empty ifc);

Reg#(Bool) r <- mkReg(False);
Reg#(Bool) s();
mkReg#(True) the_s(s, reset_by(rst));

endmodule

(* synthesize *)
module sysInputClock(Clock clk, Reset rst, Empty ifc);

Clock c <- exposeCurrentClock;
Reg#(Bool) r <- mkReg(False);
Reg#(Bool) s();
mkReg#(sameFamily(clk,c)) the_s(s, clocked_by(clk), reset_by(rst));

endmodule

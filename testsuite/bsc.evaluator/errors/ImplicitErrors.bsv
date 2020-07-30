(* synthesize *)
module sysImplicitErrors();

  Reg#(Bool) b <- mkRegU;

  Clock c <- exposeCurrentClock;
 
  Clock c_b = when(b, c);

  Reg#(Bit#(32)) blob <- mkRegU(clocked_by c_b);

  Reset r <- exposeCurrentReset;

  Reset r_b = when(b, r);

  Reg#(Bit#(32)) blob0 <- mkReg(0, reset_by r_b);

endmodule


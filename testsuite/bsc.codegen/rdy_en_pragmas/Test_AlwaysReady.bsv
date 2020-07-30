
(* synthesize *)
(* always_ready *)
(* gate_input_clocks = "default_clock" *)
module sysTest_AlwaysReady(Reg#(Bool));
   Reg#(Bool) rg <- mkReg(True);

   method _read = rg;
   method _write(x) = rg._write(x);
endmodule


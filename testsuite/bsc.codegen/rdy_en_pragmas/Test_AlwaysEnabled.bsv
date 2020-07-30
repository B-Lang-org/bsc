
(* synthesize *)
(* always_enabled, always_ready *)
(* gate_input_clocks = "default_clock" *)
module mkSub(Reg#(Bool));
   Reg#(Bool) rg <- mkReg(True);
   return (rg);
endmodule

(* synthesize *)
(* gate_input_clocks = "default_clock" *)
module sysTest_AlwaysEnabled();
   Reg#(Bool) rg <- mkSub;

   rule r1;
      rg <= False;
   endrule

   rule r2;
      $display("rg = %d", rg);
   endrule
endmodule


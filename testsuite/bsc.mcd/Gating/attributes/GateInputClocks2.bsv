// Test that multiple attributes are OK

(* synthesize *)
(* gate_input_clocks="c2" *)
(* gate_input_clocks="c1" *)
module sysGateInputClocks2 #(Clock c1, Clock c2, Clock c3) ();
endmodule


(* synthesize *)
(* no_default_reset *)
module mkEUseDefaultReset_OK();
   // mkRegU doesn't use the reset, so there should be no error
   Reg#(Bit#(32)) r <- mkRegU();
endmodule

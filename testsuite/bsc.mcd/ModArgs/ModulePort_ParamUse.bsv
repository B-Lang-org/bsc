
(* synthesize *)
module sysModulePort_ParamUse #(Bit#(32) x) ();

   Empty i <- mkModulePort_ParamUse_Sub (x);

endmodule

(* synthesize *)
module mkModulePort_ParamUse_Sub #(parameter Bit#(32) x) ();

   Reg#(Bit#(32)) rg <- mkRegU();

   rule r;
      rg <= x;
   endrule

endmodule

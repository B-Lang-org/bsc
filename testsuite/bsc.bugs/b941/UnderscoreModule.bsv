(* synthesize *)
module sysUnderscoreModule_ (Reg#(Bool));
   Reg#(Bool) rg <- mkRegU;
   return rg;
endmodule

(* synthesize *)
module sysUnderscoreModule (Reg#(Bool));
   Reg#(Bool) rg <- mkRegU;
   return rg;
endmodule

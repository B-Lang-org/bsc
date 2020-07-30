(* synthesize *)
module sysUnderscore (Reg#(Bool));
   let s <- mkUnderscore_;
   return s;
endmodule

(* synthesize *)
module mkUnderscore_ (Reg#(Bool));
   Reg#(Bool) rg_ <- mkRegU;
   return rg_;
endmodule


module mkSub (Reg#(UInt#(16)) rg, Empty ifc);
   (* descending_urgency = "sub_r, r" *)
   rule sub_r;
      rg <= rg + 2;
   endrule
endmodule

(* synthesize *)
module sysRuleNameInSubmod ();
   Reg#(UInt#(16)) rg <- mkRegU;

   rule r;
      rg <= rg + 1;
   endrule

   Empty s <- mkSub(rg);
endmodule


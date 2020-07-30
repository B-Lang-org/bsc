module mkSub (Reg#(UInt#(16)) rg, Empty ifc);
   rule sub_r;
      rg <= rg + 2;
   endrule
endmodule

(* synthesize *)
module sysRuleNameInParent ();
   Reg#(UInt#(16)) rg <- mkRegU;

   Empty s <- mkSub(rg);

   (* descending_urgency = "s_sub_r, r" *)
   rule r;
      rg <= rg + 1;
   endrule
endmodule


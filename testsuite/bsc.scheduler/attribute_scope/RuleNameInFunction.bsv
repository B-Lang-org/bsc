function Rules fn(Reg#(UInt#(16)) rg);
   return (rules
              (* descending_urgency = "fn_r, r" *)
              rule fn_r;
                 rg <= rg + 2;
              endrule
           endrules);
endfunction

(* synthesize *)
module sysRuleNameInFunction ();
   Reg#(UInt#(16)) rg <- mkRegU;

   rule r;
      rg <= rg + 1;
   endrule

   addRules(fn(rg));
endmodule


interface Ifc;
   interface Empty e;
endinterface

(* synthesize *)
module sysRuleIUNotUsed(Ifc);
   Rules rs = emptyRules;
   let x <- addRules(rs);
   interface e = x;
endmodule

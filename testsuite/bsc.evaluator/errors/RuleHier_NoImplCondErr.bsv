
(* synthesize *)
module sysRuleHier_NoImplCondErr();
   let m1 <- mkSub1;
endmodule

module mkSub1();
   let m2 <- mkSub2;
endmodule

module mkSub2();
   Wire#(Bool)   w  <- mkWire;
   Reg#(Bool)    rg <- mkRegU;

   (* no_implicit_conditions *)
   rule r;
      rg <= w;
   endrule
endmodule


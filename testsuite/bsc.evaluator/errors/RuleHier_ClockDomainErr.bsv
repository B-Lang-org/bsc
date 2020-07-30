(* synthesize *)
module sysRuleHier_ClockDomainErr(Clock clk2, Empty ifc);
   let m1 <- mkSub1(clk2);
endmodule

module mkSub1(Clock clk2, Empty ifc);
   let m2 <- mkSub2(clk2);
endmodule

module mkSub2(Clock clk2, Empty ifc);
   Reg#(Bool) rg1 <- mkRegU;
   Reg#(Bool) rg2 <- mkRegU(clocked_by clk2);

   rule r;
      rg1 <= rg2;
   endrule
endmodule


import Clocks::*;

(* synthesize *)
module sysRuleHier_ClockCrossRuleErr();
   let m1 <- mkSub1;
endmodule

module mkSub1();
   let m2 <- mkSub2;
endmodule

module mkSub2();
   Wire#(Bool)   w  <- mkWire;
   Reg#(Bool)    rg <- mkRegU;

   // This fails because it implies "no_implicit_conditions"
   (* clock_crossing_rule *)
   rule r;
      rg <= w;
   endrule
endmodule


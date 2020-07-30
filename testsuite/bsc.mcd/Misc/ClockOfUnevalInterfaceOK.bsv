interface TwoClockIfc;
   method Bool c1_m1();
   method Bool c1_m2();
   method Bool c2_m1();
   method Bool c2_m2();
endinterface

module mkTwoClock#(Clock clk2) (TwoClockIfc);
   Reg#(Bool) c1_r1 <- mkRegU;
   Reg#(Bool) c1_r2 <- mkRegU;

   Reg#(Bool) c2_r1 <- mkRegU(clocked_by clk2);
   Reg#(Bool) c2_r2 <- mkRegU(clocked_by clk2);

   method c1_m1 = c1_r1;
   method c1_m2 = c1_r2;

   method c2_m1 = c2_r1;
   method c2_m2 = c2_r2;
endmodule

function Tuple2#(Bool,Bool) getC1(TwoClockIfc i);
   return tuple2(i.c1_m1, i.c1_m2);
endfunction

function Tuple2#(Bool,Bool) getC2(TwoClockIfc i);
   return tuple2(i.c2_m1, i.c2_m2);
endfunction

(* synthesize *)
module sysClockOfUnevalInterfaceOK #(Clock clk2) ();
   Clock clk1 <- exposeCurrentClock;

   let m <- mkTwoClock(clk2);
   Tuple2#(Bool,Bool) p1 = getC1(m);
   Tuple2#(Bool,Bool) p2 = getC2(m);

   Clock c1 = clockOf(p1);  // = clk1;
   Reg#(Tuple2#(Bool,Bool)) rg1 <- mkRegU(clocked_by c1);
   rule r1;
      rg1 <= p1;
   endrule

   Clock c2 = clockOf(p2);  // = clk2;
   Reg#(Tuple2#(Bool,Bool)) rg2 <- mkRegU(clocked_by c2);
   rule r2;
      rg2 <= p2;
   endrule
endmodule

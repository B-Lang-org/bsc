import Clocks::*;

function Action check(String test, Clock c1, Clock c2, Bool expected);
   let res = (isAncestor(c1,c2) == expected) ? "OK" : "FAIL";
   $display("%s: %s", res, test);
endfunction 

(* synthesize *)
module sysIsAncestor();

   Clock clk1 <- exposeCurrentClock();

   GatedClockIfc gc1 <- mkGatedClock(True, clk1);
   Clock clk1_1 = gc1.new_clk;

   GatedClockIfc gc2 <- mkGatedClock(True, clk1);
   Clock clk1_2 = gc2.new_clk;
   
   GatedClockIfc gc11 <- mkGatedClock(True, clk1_1);
   Clock clk1_1_1 = gc11.new_clk;

   GatedClockIfc gc12 <- mkGatedClock(True, clk1_1);
   Clock clk1_1_2 = gc12.new_clk;
   
   GatedClockIfc gc21 <- mkGatedClock(True, clk1_2);
   Clock clk1_2_1 = gc21.new_clk;

   GatedClockIfc gc22 <- mkGatedClock(True, clk1_2);
   Clock clk1_2_2 = gc22.new_clk;   
   
   Clock clk2 <- mkAbsoluteClock(7,15);
   
   // check that isAncestor is a reflexive, transitive, antisymmetric relation
   rule r1;
      check("reflexive on clk1", clk1, clk1, True);
      check("reflexive on clk1_1_2", clk1_1_2, clk1_1_2, True);
      check("reflexive on clk1_2_1", clk1_2_1, clk1_2_1, True);
      check("reflexive on clk2", clk2, clk2, True);
      check("clk1 AOF clk1_2", clk1, clk1_2, True);
      check("antisymmetric (clk1_2 NOT AOF clk1)", clk1_2, clk1, False);
      check("clk1_1 AOF clk1_1_1", clk1_1, clk1_1_1, True);
      check("antisymmetric (clk1_1_1 NOT AOF clk1_1)", clk1_1_1, clk1_1, False);
      check("clk1_2 AOF clk1_2_2", clk1_2, clk1_2_2, True);
      check("transitive (clk1 AOF clk1_2_2)", clk1, clk1_2_2, True);
      check("antisymmetric (clk1_2_2 NOT AOF clk1)", clk1_2_2, clk1, False);
      check("unrelated (clk1 NOT AOF clk2)", clk1, clk2, False);
      check("unrelated (clk2 NOT AOF clk1)", clk2, clk1, False);
      check("unrelated (clk1_1 NOT AOF clk1_2)", clk1_1, clk1_2, False);
      check("unrelated (clk1_2 NOT AOF clk1_1)", clk1_2, clk1_1, False);
      check("unrelated (clk1_2_1 NOT AOF clk1_1)", clk1_2_1, clk1_1, False);
      check("unrelated (clk1_1 NOT AOF clk1_2_1)", clk1_1, clk1_2_1, False);
      check("unrelated (clk1_1_1 NOT AOF clk1_2_2)", clk1_1_1, clk1_2_2, False);
      check("unrelated (clk1_2_2 NOT AOF clk1_1_1)", clk1_2_2, clk1_1_1, False);
      $finish(0);
   endrule
   
endmodule



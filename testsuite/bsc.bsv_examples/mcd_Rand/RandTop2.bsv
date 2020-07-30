import RandGen::*;
import RandUser1::*;
import RandUser2::*;
import Connectable::*;
import GetPut::*;
import RandGlobal::*;
import LBus::*;

interface ExtIfc;
   interface Component2 ifcA;
   interface Component2 ifcB;
endinterface: ExtIfc


module [MyLbSModule] mkRandTop(ExtIfc);
   // Control registers to control gating, set from the local bus:
   Reg#(Bool) g0();
   mkLbRegRW#('h404, 0, True) the_g0(g0);
   Reg#(Bool) g1();
   mkLbRegRW#('h404, 1, True) the_g1(g1);

   // Declare the gated clocks:
   GatedClockIfc gate0();
   mkGatedClockFromCC the_g(True, gate0);
   (* fire_when_enabled *)
   rule upd_gate;
      gate0.setGateCond(g0);
   endrule
   Clock c0 = gate0.new_clk;

   GatedClockIfc gate1();
   mkGatedClockFromCC the_g(True, gate1);
   (* fire_when_enabled *)
   rule upd_gate;
      gate1.setGateCond(g1);
   endrule
   Clock c1 = gate1.new_clk;

   // The clock for the generator, on if either consumer is on:
   GatedClockIfc gate2();
   mkGatedClockFromCC the_g(True, gate2);
   (* fire_when_enabled *)
   rule upd_gate;
      gate2.setGateCond(g0 || g1);
   endrule
   Clock c2 = gate2.new_clk;
   
   // Instantiate the sub-modules, appropriately clocked:
   GenPair gens();
   mkSplitter the_gens(gens, clocked_by c2);

   UserIfc user1();
   mkRUser1 the_user1(user1, clocked_by c0);

   UserIfc user2();
   mkRUser2 the_user2(user2, clocked_by c1);

   // Since all the clocks are in the same family, there is no need for
   // explicit conversions (it is all handled by implicit conditions):
   mkConnection(gens.fst, user1.fst);
   mkConnection(gens.snd, user2.fst);

   interface ifcA = user1.snd;
   interface ifcB = user2.snd;
endmodule

// LBus bureaucracy to be added.

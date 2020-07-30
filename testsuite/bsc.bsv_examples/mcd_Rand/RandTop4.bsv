//    mkConvGetPut(Clock c1, Clock c2, GetPut#(a) i);
//  The interface provided by the submodule is Put#(Bit#(6))

import RandGen::*;
import RandUser1::*;
import RandUser2::*;
import Connectable::*;
import GetPut::*;
import RandGlobal::*;
import LBus::*;

// A module to produce a slower clock.
module mkSlowClock(UInt#(4) fraction, Bool gate, Clock c);
   // exactly as before:
   . . .
endmodule

// Since subinterface ifcB is to be clocked by the new slower clock, we must
// also export the clock itself, for otherwise ifcB will be unusable
// externally.
interface ExtIfc;
   interface Component2 ifcA;
   interface Component2 ifcB;
   interface Clock cB;
endinterface: ExtIfc

module [MyLbSModule] mkRandTop(ExtIfc);
   // Control registers to control gating, set from the local bus:
   Reg#(Bool) g0();
   mkLbRegRW#('h404, 0, True) the_g0(g0);
   Reg#(Bool) g1();
   mkLbRegRW#('h404, 1, True) the_g1(g1);
   // And a control register for the fractional frequency of the slower clock:
   Reg#(Bit#(4)) fr();
   mkLbRegRW#('h404, 4, 2) the_fr(fr);
   
   // Declare the gated clocks:
   GatedClockIfc gate0();
   mkGatedClockFromCC the_g(True, gate0);
   (* fire_when_enabled *)
   rule upd_gate;
      gate0.setGateCond(g0);
   endrule
   Clock c0 = gate0.new_clk;
   // c1 will be a slower clock:
   Clock c1();
   mkSlowClock gate2(fr, g1, c1);

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

   // Since c0 and c1 are in the same family, there is no need for
   // explicit conversion:
   mkConnection(gens.fst, user1.fst);

   // c2 is unrelated to c0, however, so explicit conversion is necessary.
   // This version uses the "hardware approach" described in the Methodology
   // document.  

   // This will create a GetPut pair of interfaces for the Bit#(6) type, with
   // the Get clocked by c2, and the Put clocked by c1:
   GetPut#(Bit#(6)) conv_gp();
   mkConvGetPut the_user2_converter(c2, c1, conv_gp);
   // Then we can connect the Get subinterface to the Put from user2, and the
   // Put one to the Get from gens, since the clocks for the pairs to be
   // connected together are now the same:
   mkConnection(conv_gp.fst, user2.fst);
   mkConnection(conv_gp.snd. gens.snd);

   interface ifcA = user1.snd;
   interface ifcB = user2.snd;
   // Export the clock for ifcB:
   interface cB = c1;
endmodule

// LBus bureaucracy to be added.



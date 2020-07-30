import RandGen::*;
import RandUser1::*;
import RandUser2::*;
import Connectable::*;
import GetPut::*;
import RandGlobal::*;
import LBus::*;
import Clocks::*;

// A module to produce a slower clock.  Sub-multiple of frequency dynamically
// variable, so controlled by a dynamic argument.
module mkSlowClock(UInt#(4) fraction, Bool gate, Clock c);
   Reg#(UInt#(4)) count():
   mkReg#(0) the_count(count);

   Reg#(Bit#(1)) osc();
   mkReg#(0) the_osc(osc);

   // Make the new clock, using osc and the gate argument:
   Clock new_c();
   mkClock the_new_c(osc, gate, new_c);

   // Rules to produce the new oscillation:
   (* no_implicit_conditions, fire_when_enabled)
   rule dec (count != 0);
      count <= count - 1;
   endrule
   
   (* no_implicit_conditions, fire_when_enabled)
   rule change (count == 0);
      osc <= invert(osc);

      // Treat invalid argument values (<2) as if 2:
      let up = (fraction>1 ? fraction>>1 : 1);
      let down = (fraction>1 ? fraction-up : 1);

      count <= (osc==0 ? up : down);
   endrule

   return (new_c);
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

   // Since c0 and c1 are in the same family, there is no need for
   // explicit conversion:
   mkConnection(gens.fst, user1.fst);

   // c2 is unrelated to c0, however, so explicit conversion is necessary.
   // This version uses the "linguistic approach" described in the Methodology
   // document.  

   let user2ifc();
   // There's no need to specify an explicit clock for the converter, since
   // the current clock is in the same family as c0.  But "clocked_by c0"
   // could be added to the argument list if preferred:
   mkConverter the_user2_converter(user2.fst, user2ifc /*, clocked_by c0 */);
   
   mkConnection(gens.snd, user2ifc);

   interface ifcA = user1.snd;
   interface ifcB = user2.snd;
   // Export the clock for ifcB:
   interface cB = c1;
endmodule

// LBus bureaucracy to be added.



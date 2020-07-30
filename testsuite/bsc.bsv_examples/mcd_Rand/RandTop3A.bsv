import RandGen::*;
import RandUser1::*;
import RandUser2::*;
import Connectable::*;
import GetPut::*;
import RandGlobal::*;
import Clocks::*;

// A module to produce a slower clock.  Sub-multiple of frequency dynamically
// variable, so controlled by a dynamic argument.
module mkSlowClock(UInt#(4) fraction, Bool gate, Clock c);
   Reg#(UInt#(4)) count();
   mkReg#(0) the_count(count);

   Reg#(Bit#(1)) osc();
   mkReg#(0) the_osc(osc);

   // Make the new clock, using osc and the gate argument:
   Clock new_c();
   mkClock the_new_c(osc, gate, new_c);

   // Rules to produce the new oscillation:
   (* no_implicit_conditions, fire_when_enabled *)
   rule dec (count != 0);
      count <= count - 1;
   endrule
   
   (* no_implicit_conditions, fire_when_enabled *)
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

(* synthesize *)
module mkRandTop(UInt#(4) fr, Bool g0, Bool g1, Bool g2, ExtIfc ifc);
   // Declare the gated clocks:
   GatedClockIfc gate1();
   mkGatedClockFromCC the_g1(True, gate1);
   (* fire_when_enabled *)
   rule upd_gate1;
      gate1.setGateCond(g1);
   endrule
   Clock c1 = gate1.new_clk;
   // c2 will be a slower clock:
   Clock c2();
   mkSlowClock gate2(fr, g2, c2);
   // it accordingly needs a reset associated with it:
   Reset r2();
   mkSyncResetFromCR#(0) the_r2(c2, r2);
   
   // The clock for the generator, on if either consumer is on:
   GatedClockIfc gate0();
   mkGatedClockFromCC the_g0(True, gate0);
   (* fire_when_enabled *)
   rule upd_gate0;
      gate0.setGateCond(g1 || g2);
   endrule
   Clock c0 = gate0.new_clk;
   
   // Instantiate the sub-modules, appropriately clocked:
   GenPair gens();
   mkSplitter the_gens(gens, clocked_by c0);

   UserIfc user1();
   mkRUser1 the_user1(user1, clocked_by c1);

   UserIfc user2();
   mkRUser2 the_user2(user2, clocked_by c2, reset_by r2);

   // Since c1 and c0 are in the same family, there is no need for
   // explicit conversion:
   mkConnection(gens.fst, user1.fst);

   // c2 is unrelated to c0, however, so explicit conversion is necessary.
   // This version uses the "linguistic approach".

   let user2ifc();
   // There's no need to specify an explicit clock for the converter, since
   // the current clock is in the same family as c1.
   mkConverter the_user5_converter(4, user2.fst, user2ifc);
   
   mkConnection(gens.snd, user2ifc);

   interface ifcA = user1.snd;
   interface ifcB = user2.snd;
   // Export the clock for ifcB:
   interface cB = c2;
endmodule

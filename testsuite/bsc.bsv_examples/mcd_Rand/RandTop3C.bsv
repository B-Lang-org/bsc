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
   interface Clock cA;
endinterface: ExtIfc

(* synthesize *)
module mkRandTop(UInt#(4) fr, Bool g1, Bool g2, ExtIfc ifc);
   // Declare the gated clocks and their associated resets:
   // c1 will be a slower clock:
   Clock c1(); mkSlowClock gate1(fr, g1, c1);
   Reset r1(); mkSyncResetFromCR#(3) the_r1(c1, r1);
   // c2 is a gated version of the current clock:
   GatedClockIfc gate2();
   mkGatedClockFromCC the_g2(True, gate2);
   (* fire_when_enabled *)
   rule upd_gate2;
      gate2.setGateCond(g2);
   endrule
   Clock c2 = gate2.new_clk;
   Reset r2(); mkSyncResetFromCR#(3) the_r2(c2, r2);
   // c0 is similar, on when either of the consumers is on:
   GatedClockIfc gate0();
   mkGatedClockFromCC the_g0(True, gate0);
   (* fire_when_enabled *)
   rule upd_gate0;
      gate0.setGateCond(g1 || g2);
   endrule
   Clock c0 = gate0.new_clk;
   Reset r0(); mkSyncResetFromCR#(3) the_r0(c0, r0);
   
   // Instantiate the sub-modules, appropriately clocked:
   GenPair gens();
   mkSplitter the_gens(gens, clocked_by c0, reset_by r0);

   UserIfc user1();
   mkRUser1 the_user1(user1, clocked_by c1, reset_by r1);

   UserIfc user2();
   mkRUser2 the_user2(user2, clocked_by c2, reset_by r2);

   // Since c2 and c0 are in the same family, there is no need for
   // explicit conversion:
   mkConnection(gens.fst, user2.fst);

   // c1 is unrelated to c0, however, so explicit conversion is necessary.
   // This version uses the "hardware approach".


   SyncFIFOIfc#(Bit#(6)) ff();
   mkSyncFIFO#(4) the_ff(c0,r0, c1, ff);

   // Then we provide two rules to enqueue values from the generator onto ff,
   // and to dequeue them to send to user1:
   rule enqueue_ff;
      let x <- gens.snd.get;
      ff.enq(x);
   endrule
   rule dequeue_ff;
      user1.fst.put(ff.first);
      ff.deq;
   endrule

   interface ifcA = user1.snd;
   interface ifcB = user2.snd;
   // Export the clock for ifcA:
   interface cA = c1;
endmodule

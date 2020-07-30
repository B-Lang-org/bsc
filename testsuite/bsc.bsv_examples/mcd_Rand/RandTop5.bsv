import RandGen::*;
import RandUser1::*;
import RandUser2::*;
import Connectable::*;
import GetPut::*;
import RandGlobal::*;
import Clocks::*;

interface ExtIfc;
   interface Component2 ifcA;
   interface Component2 ifcB;
endinterface: ExtIfc

(* synthesize *)
(* gate_all_clocks *)
module mkRandTop(Clock c1, Reset r1,
		 Clock c2, Reset r2,
		 ExtIfc ifc);
   
   GenPair gens();
   mkSplitter the_gens(gens); // clocked and reset by mkRandTop's defaults

   UserIfc user1();
   mkRUser1 the_user1(user1, clocked_by c1, reset_by r1);

   UserIfc user2();
   mkRUser2 the_user2(user2, clocked_by c2, reset_by r2);

   let user1ifc <- mkConverter(4, user1.fst);
   let user2ifc <- mkConverter(4, user2.fst);
   
   mkConnection(gens.fst, user1ifc);
   mkConnection(gens.snd, user2ifc);

   interface ifcA = user1.snd;
   interface ifcB = user2.snd;
endmodule

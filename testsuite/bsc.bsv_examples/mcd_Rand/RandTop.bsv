import RandGen::*;
import RandUser1::*;
import RandUser2::*;
import Connectable::*;
import GetPut::*;
import RandGlobal::*;

interface ExtIfc;
   interface Component2 ifcA;
   interface Component2 ifcB;
endinterface: ExtIfc

(* synthesize *)
module mkRandTop(ExtIfc);
   GenPair gens();
   mkSplitter the_gens(gens);

   UserIfc user1();
   mkRUser1 the_user1(user1);

   UserIfc user2();
   mkRUser2 the_user2(user2);

   mkConnection(gens.fst, user1.fst);
   mkConnection(gens.snd, user2.fst);

   interface ifcA = user1.snd;
   interface ifcB = user2.snd;
endmodule




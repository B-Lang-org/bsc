import RandGenC::*;
import RandUser1C::*;
import RandUser2C::*;
import Connectable::*;
import CGetPut::*;
import RandGlobalC::*;

(* synthesize *)
module mkRandTop(Tuple2#(Component2,Component2));
   GenPair gens();
   mkSplitter the_gens(gens);

   UserIfc user1();
   mkRUser1 the_user1(user1);

   UserIfc user2();
   mkRUser2 the_user2(user2);

   mkConnection(gens.fst, user1.fst);
   mkConnection(gens.snd, user2.fst);

   return tuple2(user1.snd, user2.snd);
endmodule




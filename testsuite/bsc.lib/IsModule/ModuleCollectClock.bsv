import ModuleCollect::*;
import List::*;

typedef ModuleCollect#(Integer) Module2;

module [Module2] mkTest#(Clock c)();
   Reg#(Bit#(32)) r <- mkRegU(clocked_by c);

   addToCollection(5);
   
   rule test;
      r <= r + 1;
   endrule
   
endmodule

(* synthesize *)
module [Module] mkTestWrapper#(Clock c)();
   
   let _m <- exposeCollection(mkTest(c));

   mapM(messageM,map(integerToString, _m.collection));
   
endmodule

   

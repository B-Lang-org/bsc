import GetPut :: * ;
import Connectable :: * ;

// clk1 and clk2 are in the same family generated via a clock tree!

// A tuple (GetPut) is not a valid module interface, so expose the Get/Put
// sides through a named interface instead.
interface GetPutIfc;
   interface Get#(int) fst;
   interface Put#(int) snd;
endinterface

(* synthesize *)
(* clock_family = "clk1, clk2" *)
module mkGP ( Clock clk1, Clock clk2, GetPutIfc ifc ) ;


   GetPut#(int) gp1 <- mkGPFIFO( clocked_by clk1, reset_by noReset  ) ;
   GetPut#(int) gp2 <- mkGPFIFO( clocked_by clk2, reset_by noReset  ) ;

   mkConnection( gp1.snd, gp2.fst );

   interface Get fst = gp1.fst ;
   interface Put snd = gp2.snd ;

endmodule

import GetPut :: * ;
import Connectable :: * ;

// clk1 and clk2 are in the same family generated via a clock tree!

(* synthesize *)
(* clock_family = "clk1, clk2" *)
module mkGP ( Clock clk1, Clock clk2, GetPut#(int) ifc ) ;
   
   
   GetPut#(int) gp1 <- mkGPFIFO( clocked_by clk1, reset_by noReset  ) ;
   GetPut#(int) gp2 <- mkGPFIFO( clocked_by clk2, reset_by noReset  ) ;
   
   mkConnection( gp1.snd, gp2.fst );
   
   interface Get fst = gp1.fst ;
   interface Put snd = gp2.snd ;
   
endmodule

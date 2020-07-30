import ListN::*;

typedef struct {
   Int#(32) a;
   ListN#(3, Int#(32)) bs;
   } ABs deriving (Eq, Bits);

(* synthesize *)
module mkStructListNUninitErr();
   ABs bar;
   bar.a = 0;
   
   rule test;
     $display(bar);
     $finish(0);
   endrule

endmodule
 

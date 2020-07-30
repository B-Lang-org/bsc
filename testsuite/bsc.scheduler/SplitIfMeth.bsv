// check scheduling annotations for split methods
// a and b should conflict because:
/// a1_T SB a2 and a2 SB a1_F
interface Split;
  method Action a1;
  method Action a2;
endinterface

(* synthesize *)
module mkSplitIfMeth(Split);
  
  Reg#(int)  x <- mkRegU;
  Reg#(int)  y <- mkRegU;
  Reg#(int)  z <- mkRegU;
  Reg#(Bool) b <- mkRegU;

  method Action a1;
    (* split *)
    if (b)
      x <= y;
    else 
      z <= x;
  endmethod
  
  method Action a2;
    y <= z; 
  endmethod

endmodule


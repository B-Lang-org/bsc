//Testcase 
import ConfigReg::*;

(* synthesize *)
module sysDesign (Empty);
 Reg#(Bit#(2))    x <- mkConfigRegA(0);

   (* descending_urgency = "w1, incr"  *)
 rule w1 (True);
    x <= 1;
    $display( "set rule" ) ;
 endrule

 rule incr (True);
    x <= x + 1;
    $display( "incr rule %0d", x ) ;
 endrule

 rule fin ( x >= 3);
    $display( "successful compile and link" ) ;
    $finish(0);
 endrule


   
endmodule

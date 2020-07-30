import List::*;

(* synthesize *)
module sysListDesugar();

   List#(Reg#(Bit#(40))) regs <- replicateM(5, mkReg(40'hdeadbeef00));
   
   rule test;
      $display("%h", regs[3]);
      $finish(0);
   endrule
   
endmodule

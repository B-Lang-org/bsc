import List::*;

module sysListDesugarFail();

   List#(Reg#(Bit#(40))) regs <- replicateM(5, mkReg(40'hdeadbeef00));
   
   rule test;
      $display("%h", 16'hffff + regs[3]);
      $finish(0);
   endrule
   
endmodule

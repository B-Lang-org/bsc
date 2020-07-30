import List::*;

module sysListDesugarFail2();

   List#(Reg#(Bool)) regs <- replicateM(5, mkReg(False));
   
   rule test;
      Bit#(16) test = 16'hffff + regs[3];
      $display(test);
      $finish(0);
   endrule
   
endmodule

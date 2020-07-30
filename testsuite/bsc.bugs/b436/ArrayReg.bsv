// test that sensible read and write syntax for arrays of regs works together

module test();

   Reg#(Bit#(32)) pipe[2];
   
   rule move;
      pipe[0] <= pipe[1];
   endrule
   
endmodule

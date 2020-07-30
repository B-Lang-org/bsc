module sysTest(Empty);
   Reg#(Bool) xs[8];
   for (Integer i=0; i<8; i=i+1)
      xs[i] <- mkReg(False);

   rule r (True);
      xs[0] <= True;
   endrule
endmodule

module sysPrintTime(Empty);
   Reg#(Bit#(16)) r();
   mkReg#(0) the_r(r);

   rule count
    (True); r <= r + 1;
   endrule
   rule display
    (True); 
      action
         Bit#(64) t <- $time();
         Bit#(32) test1 <- $stime();
         Bit#(64) test2 <- $time();
         $display("Time %0d: %t", r, t);
         $display("Test: %t, %t", test1, test2);
      endaction
   endrule
   rule finish
    (r == 5); $finish(0);
   endrule
endmodule

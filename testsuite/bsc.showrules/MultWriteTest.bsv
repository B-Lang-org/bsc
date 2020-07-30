(* synthesize *)
module mkMultWriteTest();

   Reg#(UInt#(8)) count  <- mkReg(0);
   Reg#(UInt#(8)) count2 <- mkReg(0);
   
   rule incr;
      count <= count + 1;
   endrule

   rule bump (count % 2 == 1);
      count2 <= count2 + 2;
   endrule
   
   rule restart (count % 10 == 9);
      count2 <= 1;
   endrule
   
   rule done (count > 100);
      $finish(0);
   endrule
   
endmodule

(* synthesize *)

module mkTest();

   Bool b;
   for(Integer i = 0; i < 12; i = i + 1)
      b = !b;
   Reg#(Bool) r <- mkReg(b);

   rule test;
      $display(b);
      $finish(0);
   endrule
   
endmodule

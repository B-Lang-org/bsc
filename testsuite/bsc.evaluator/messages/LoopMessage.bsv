(* synthesize *)
module sysLoopMessage(Empty);
   
   for(Integer i = 0; i < 8; i = i + 1)
      messageM("Testing sysLoopMessage...");
   
   rule test;
      $finish(0);
   endrule
   
endmodule

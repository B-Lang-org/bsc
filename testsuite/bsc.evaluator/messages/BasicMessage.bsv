(* synthesize *)
module sysBasicMessage(Empty);

   messageM("Testing sysBasicMessage...");

   rule test;
      $finish(0);
   endrule
   
endmodule

(* synthesize *)
module mkStringParamErr#(String s)();

   rule test;
      $display(s);
      $finish(0);
   endrule
   
endmodule

(* synthesize *)
module mkRealParamErr1#(real r)();
   
   rule test;
      $display(r);
      $finish(0);
   endrule

endmodule

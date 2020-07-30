(* synthesize *)
module sysModByZero();
   rule test;
      $display(mod(5,0));
      $finish(0);
   endrule
endmodule

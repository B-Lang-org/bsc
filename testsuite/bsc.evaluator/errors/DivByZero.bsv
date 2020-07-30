(* synthesize *)
module sysDivByZero();
   rule test;
      $display(div(5,0));
      $finish(0);
   endrule
endmodule

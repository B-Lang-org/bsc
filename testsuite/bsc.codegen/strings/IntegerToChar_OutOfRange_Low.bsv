(* synthesize *)
module sysIntegerToChar_OutOfRange_Low();
   rule r;
      $display(integerToChar(-1));
   endrule
endmodule

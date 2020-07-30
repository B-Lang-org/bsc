(* synthesize *)
module sysIntegerToChar_OutOfRange_High();
   rule r;
      $display(integerToChar(256));
   endrule
endmodule

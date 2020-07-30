(* synthesize *)
module sysUndefinedStringLength();

   String s = ?;

   rule test;
     $display(stringLength(s));
   endrule

endmodule
 
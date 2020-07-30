(* synthesize *)
module sysStringSelect_OutOfRange();
   rule r;
      String str = "foo";
      $display(str[3]);
   endrule
endmodule

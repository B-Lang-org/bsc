(* synthesize *)
module sysStringUpdate_OutOfRange();
   rule r;
      String str = "foo";
      str[3] = "d";
      $display(str);
   endrule
endmodule

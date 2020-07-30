(* synthesize *)
module sysCharLiteralOK();
   rule r;
      Char c = "w";
      $display(c);
   endrule
endmodule


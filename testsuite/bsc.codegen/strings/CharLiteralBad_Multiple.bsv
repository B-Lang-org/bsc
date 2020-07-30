(* synthesize *)
module sysCharLiteralBad_Multiple();
   rule r;
      Char c = "wx\t\n\f\v\x0D\xA0";
      $display(c);
   endrule
endmodule


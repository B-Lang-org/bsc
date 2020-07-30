(* synthesize *)
module sysCharLiteralBad_Empty();
   rule r;
      Char c = "";
      $display(c);
   endrule
endmodule


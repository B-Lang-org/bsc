(* synthesize *)
module sysDigitToBits_BadResultSize();
   rule r;
      Bit#(1) v = digitToBits("2");
      $display(v);
   endrule
endmodule

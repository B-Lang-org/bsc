(*synthesize*)
module sysSWrite64();

   rule r;
      Bit#(64) x <- $swriteAV("12345678");
      $display("%x", x);
      $finish;
   endrule

endmodule
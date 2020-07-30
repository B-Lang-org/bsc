Integer x = -1;
UInt#(5) y = fromInteger(x);

(* synthesize *)
module sysNegativeUIntTest();

   rule test;
      $display(y);
      $finish(0);
   endrule

endmodule

(* synthesize *)
module sysEmptyFormat ();
   rule go;
      Fmt f = $format();
      $display(f);
   endrule
endmodule


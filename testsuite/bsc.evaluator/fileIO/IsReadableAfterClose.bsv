(* synthesize *)
module sysIsReadableAfterClose();
   Handle h <- openFile("sysBasicRead.txt", ReadMode);

   Bool b <- hIsReadable(h);
   rule do_disp1;
      $display(b);
   endrule

   hClose(h);

   // Attempt to query after close
   b <- hIsReadable(h);
   rule do_disp2;
      $display(b);
   endrule

endmodule


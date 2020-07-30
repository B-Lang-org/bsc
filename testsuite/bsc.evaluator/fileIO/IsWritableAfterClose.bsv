(* synthesize *)
module sysIsWritableAfterClose();
   Handle h <- openFile("sysBasicRead.txt", ReadMode);

   Bool b <- hIsWritable(h);
   rule do_disp1;
      $display(b);
   endrule

   hClose(h);

   // Attempt to query after close
   b <- hIsWritable(h);
   rule do_disp2;
      $display(b);
   endrule

endmodule


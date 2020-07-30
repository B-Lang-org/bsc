(* synthesize *)
module sysGetCharAfterClose();
   Handle h <- openFile("sysBasicRead.txt", ReadMode);

   Char c <- hGetChar(h);
   rule do_disp1;
      $display("%c", c);
   endrule

   hClose(h);

   // Attempt to get after close
   c <- hGetChar(h);
   rule do_disp2;
      $display("%c", c);
   endrule

endmodule


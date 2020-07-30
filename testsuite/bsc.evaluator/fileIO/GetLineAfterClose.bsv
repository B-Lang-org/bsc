(* synthesize *)
module sysGetLineAfterClose();
   Handle h <- openFile("sysBasicRead.txt", ReadMode);

   String str <- hGetLine(h);
   rule do_disp1;
      $display("%s", str);
   endrule

   hClose(h);

   // Attempt to get after close
   str <- hGetLine(h);
   rule do_disp2;
      $display("%s", str);
   endrule

endmodule


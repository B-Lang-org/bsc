(* synthesize *)
module sysSetBufferingAfterClose();
   Handle h <- openFile("sysSetBufferingAfterClose.log", WriteMode);

   hPutStr(h, "Hi");

   hClose(h);

   // Attempt to set the buffering after close
   hSetBuffering(h, NoBuffering);
endmodule


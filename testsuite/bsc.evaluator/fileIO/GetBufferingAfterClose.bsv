(* synthesize *)
module sysGetBufferingAfterClose();
   Handle h <- openFile("sysGetBufferingAfterClose.log", WriteMode);

   hPutStr(h, "Hi");

   hClose(h);

   // Attempt to get the buffering after close
   BufferMode m <- hGetBuffering(h);
endmodule


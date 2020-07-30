(* synthesize *)
module sysBuffering();
   Handle h <- openFile("sysBuffering.log", WriteMode);

   // Test that the functions are available
   BufferMode m <- hGetBuffering(h);
   hSetBuffering(h, NoBuffering);
   m <- hGetBuffering(h);
   hSetBuffering(h, LineBuffering);
   m <- hGetBuffering(h);
   hSetBuffering(h, tagged BlockBuffering (tagged Invalid));
   m <- hGetBuffering(h);
   hSetBuffering(h, tagged BlockBuffering (tagged Valid 64));
   m <- hGetBuffering(h);
   // And that explicit flushing is available
   hFlush(h);

   // Attempt to test that buffered data will be written even
   // if the user doesn't close the file
   hPutStr(h, "Hi");

   //hClose(h);
endmodule


(* synthesize *)
module sysFlushAfterClose();
   Handle h <- openFile("sysFlushAfterClose.log", WriteMode);

   hPutStr(h, "Hi");

   hClose(h);

   // Attempt to flush after close
   hFlush(h);
endmodule


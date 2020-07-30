(* synthesize *)
module sysPutAfterClose();
   Handle h <- openFile("sysPutAfterClose.log", WriteMode);

   hPutStr(h, "Hi");

   hClose(h);

   // Attempt to put after close
   hPutStr(h, "Hello");
endmodule


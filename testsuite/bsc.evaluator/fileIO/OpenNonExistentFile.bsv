(* synthesize *)
module sysOpenNonExistentFile();
   Handle h <- openFile("./notadir/sysOpenNonExistentFile.log", WriteMode);

   hPutStr(h, "Hi");

   hClose(h);
endmodule


(* synthesize *)
module sysCloseTwice();
   Handle h1 <- openFile("relative.log", WriteMode);
   //Handle h2 <- openFile("/tmp/absolute.log", WriteMode);

   hPutStrLn(h1, "Relative");
   //hPutStrLn(h2, "Absolute");

   hClose(h1);
   //hClose(h2);
endmodule


(* synthesize *)
module sysCloseTwice();
   Handle h <- openFile("sysCloseTwice.log", WriteMode);

   hPutStr(h, "Hi");

   hClose(h);

   // An extra close
   hClose(h);
endmodule


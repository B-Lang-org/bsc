String fname = "sysBasicWrite.log";

(* synthesize *)
module sysBasicWrite ();
   Handle hdl <- openFile(fname, WriteMode);
   hPutStr(hdl, "Hello");
   hClose(hdl);
   mkSub;
endmodule

module mkSub ();
   Handle hdl <- openFile(fname, AppendMode);
   hPutChar(hdl, " ");
   hPutStr(hdl, "World\n");
   hClose(hdl);
endmodule


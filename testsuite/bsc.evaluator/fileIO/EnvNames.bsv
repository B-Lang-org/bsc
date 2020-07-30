(* synthesize *)
module sysEnvNames();
   Handle h <- openFile("sysEnvNames.log", WriteMode);

   hPutStrLn(h, genPackageName);
   hPutStrLn(h, genModuleName);

   hClose(h);
endmodule


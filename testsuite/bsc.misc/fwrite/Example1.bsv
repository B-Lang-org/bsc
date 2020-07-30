

(* synthesize *)
module sysExample1 () ;
   
   Reg#(int) cnt <- mkReg(0);
   let fh <- mkReg(InvalidFile) ;
   let fmcd <- mkReg(InvalidFile) ;
   
   rule open (cnt == 0 ) ;
      // Open the file and check for proper opening
      String dumpFile =  "dump_file1.dat" ;
      File lfh <- $fopen( dumpFile, "w" ) ;
      if ( lfh == InvalidFile )
         begin
            $display("cannot open %s", dumpFile);
            $finish(0);
         end
      cnt <= 1 ;
      fh <= lfh ;               // Save the file in a Register
   endrule

   rule open2 (cnt == 1 ) ;
      // Open the file and check for proper opening
      // Using a multi-channel descriptor.
      String dumpFile =  "dump_file2.dat" ;
      File lmcd <- $fopen( dumpFile ) ;
      if ( lmcd == InvalidFile )
         begin
            $display("cannot open %s", dumpFile );
            $finish(0);
         end
      lmcd = lmcd | stdout_mcd ;
      cnt <= 2 ;
      fmcd <= lmcd ;               // Save the file in a Register
   endrule

   
   rule dump (cnt > 1 );
      $fwrite( fh , "cnt = %0d\n", cnt);
      $fwrite( fmcd , "cnt = %0d\n", cnt);
      cnt <= cnt + 1;
   endrule
   
   rule finish (cnt > 15);
      $fclose( fmcd );
      $fclose( fh ) ;
      $finish(0);
   endrule
   
endmodule

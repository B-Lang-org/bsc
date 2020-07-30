
String dumpFile = "FOpen_MCD.dat.out";

(* synthesize *)
module sysFOpen_MCD () ;
   
   Reg#(int) cnt <- mkReg(0);
   let fh <- mkReg(InvalidFile) ;
   
   rule open (cnt == 0 ) ;
      $display("opening file %s", dumpFile ) ;
      // Using MCD style syntax
      File lfh <- $fopen(dumpFile ) ;
      if ( lfh == InvalidFile )
         begin
            $display("cannot open %s", dumpFile);
            $finish(0);
         end
      $display( "// Ignore:  Opened %s filehandle is %h", dumpFile, lfh );
      cnt <= 1 ;
      fh <= lfh ;
   endrule
   
   rule dump (cnt > 0 );
      $display("writing to %s %0d", dumpFile, cnt ) ;
      $fwrite( fh , "cnt = %0d\n", cnt);
      cnt <= cnt + 1;
   endrule
   
   rule finish (cnt > 15);
      $finish(0);
   endrule
   
endmodule

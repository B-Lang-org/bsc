
String dumpFile = "FWrite2.dat.out";

(* synthesize *)
module sysFWrite2 () ;
   
   Reg#(int) cnt <- mkReg(0);
   let fh <- mkReg(InvalidFile) ;
   
   rule open (cnt == 0 ) ;
      $display("opening file" ) ;
      let lfh <- $fopen(dumpFile, "w" ) ;
      if ( lfh == InvalidFile )
         begin
            $display("cannot open %s", dumpFile);
            $finish(0);
         end
      // $display( "// Ignore:  Opened %s filehandle is %h", dumpFile, lfh );
      cnt <= 1 ;
      fh <= lfh ;
   endrule
   
   rule dump (cnt > 0 );
      $display("writing to %s %0d", dumpFile, cnt ) ;
      let d = cnt - 16;
      $fwrite  ( fh , "%0d: %b %o %h", d,d,d,d ); $fwrite(fh, "\n" ) ;
      cnt <= cnt + 1;
   endrule
   
   rule finish (cnt > 35);
      $finish(0);
   endrule
   
endmodule

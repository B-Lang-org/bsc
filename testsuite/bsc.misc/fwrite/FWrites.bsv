
String dumpFile = "FWrites.dat.out";

(* synthesize *)
module sysFWrites () ;
   
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
      $fwrite  ( fh , "%0d", cnt - 16 ); $fdisplay(fh) ;
      $fwriteb ( fh ,  cnt - 16 ); $fdisplay(fh) ;
      $fwriteo ( fh ,  cnt - 16 ); $fdisplay(fh) ;
      $fwriteh ( fh ,  cnt - 16 ); $fdisplay(fh) ;
      cnt <= cnt + 1;
   endrule
   
   rule finish (cnt > 35);
      $finish(0);
   endrule
   
endmodule

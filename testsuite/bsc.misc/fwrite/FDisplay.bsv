
String dumpFile = "Fdisplays.dat.out";

(* synthesize *)
module sysFdisplays () ;
   
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
      $fdisplay  ( fh , "%0d", cnt - 16 ); 
      $fdisplayb ( fh ,  cnt - 16 ); 
      $fdisplayo ( fh ,  cnt - 16 ); 
      $fdisplayh ( fh ,  cnt - 16 ); 
      cnt <= cnt + 1;
   endrule
   
   rule finish (cnt > 35);
      $finish(0);
   endrule
   
endmodule

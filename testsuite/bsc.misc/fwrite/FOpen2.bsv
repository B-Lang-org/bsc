
String dumpFile = "FOpen2.dat.out";

(* synthesize *)
module sysFOpen2 () ;
   
   rule open ( True ) ;
      let lfh <- $fopen(dumpFile, "w" ) ;
      $fwrite( lfh, "sysFOpen2 wrote.\n" ) ;
      $fflush(  ) ;
      $fflush( lfh ) ;
      $fclose ( lfh ) ;
      $display( "Be sure to compare the file %s for the output data", dumpFile ) ;
      $finish(0);
      
   endrule
   
   
endmodule

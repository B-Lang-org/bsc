
String dumpFile = "FOpen_MCD2.dat.out";

(* synthesize *)
module sysFOpen_MCD2 () ;
   
   rule open ( True ) ;
      let lfh <- $fopen( dumpFile ) ;
      $fwrite( lfh, "sysFOpen2_MCD wrote.\n" ) ;
      $fclose ( lfh ) ;
      $display( "Be sure to compare the file %s for the output data", dumpFile ) ;
      $finish(0);
      
   endrule
   
   
endmodule


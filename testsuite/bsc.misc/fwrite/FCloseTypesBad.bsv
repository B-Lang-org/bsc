
String dumpFile1 = "FCloseTypes1.dat.out";
String dumpFile2 = "FCloseTypes2.dat.out";
String dumpFile3 = "FCloseTypes3.dat.out";

(* synthesize *)
module sysFCloseTypesBad () ;
   
   rule open ( True ) ;
      let lfh1 <- $fopen(dumpFile1 ) ;
      let lfh2 <- $fopen(dumpFile2 ) ;
      let lfh3 <- $fopen(dumpFile3 ) ;
      
      let f123 = lfh1 | lfh2 | lfh3 | stdout_mcd ;
      
      $fdisplay( f123, "writing this to all open files 1,2,3." ) ;
      $fflush() ;
      $fclose ( lfh1 | lfh2 ) ;
      $fdisplay( f123, "writing this to all open files  (just 3)." ) ;
      $fflush( f123 ) ;
      $fclose ( lfh3 ) ;
      $finish(0);
   endrule
   
   
endmodule

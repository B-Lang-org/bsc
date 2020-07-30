String dumpFile1 = "MCD_ops1.dat.out" ;
String dumpFile2 = "MCD_ops2.dat.out" ;
String dumpFile3 = "MCD_ops3.dat.out" ;

(* synthesize *)
module sysMCD_ops ();
   
   rule everything (True );
      let f1 <- $fopen( dumpFile1 ) ;
      let f2 <- $fopen( dumpFile2 ) ;
      let f3 <- $fopen( dumpFile3 ) ;
      
      let f12 = f1 | f2 ;
      let f13 = f1 | f3 ;
      let f123 = f1 | f3 | f2  ;
      let f1a = f13 & f12 ;
      let f1s = f1 | stdout_mcd ;
      let f12a = f123 & ~ f3 ;
      
      $fdisplay( f1, "f1 only") ;
      $fdisplay( f2, "f2 only") ;
      $fdisplay( f3, "f3 only") ;
      $fdisplay( f12, "f1 f2 only") ;
      $fdisplay( f13, "f1 f3 only") ;
      $fdisplay( f12a, "f1 and f2 only") ;
      $fdisplay( f1a, "f1 only") ;
      $fdisplay( f1s, "f1 and stdout only") ;
      $fdisplay( f123, "f1 f2 and f3 only") ;

      $fdisplay( f123, "Now display everything again f1 f2 and f3 only") ;

      $fdisplay( f1, "f1 only") ;
      $fdisplay( f2, "f2 only") ;
      $fdisplay( f3, "f3 only") ;
      $fdisplay( f12, "f1 f2 only") ;
      $fdisplay( f13, "f1 f3 only") ;
      $fdisplay( f12a, "f1 and f2 only") ;
      $fdisplay( f1a, "f1 only") ;
      $fdisplay( f1s, "f1 and stdout only") ;
      $fdisplay( f123, "f1 f2 and f3 only") ;

      $fclose( f1 ) ;
      $finish(0);
   endrule
   
endmodule

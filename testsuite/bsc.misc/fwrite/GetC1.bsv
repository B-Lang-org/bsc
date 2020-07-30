

String readFile = "gettests.dat";

(* synthesize *)
module sysGetC1 () ;
  
   rule open ( True ) ;
      let lfh <- $fopen(readFile, "r" ) ;
//      $fgetc( lfh );
//      $fgetc( lfh );
//      $fgetc( lfh );
      int i <- $fgetc( lfh );
      
      $display( "reading the first character from %s is '%c' %h", readFile, i, i ) ;
      $fclose ( lfh ) ;
      $finish(0);
      
   endrule
   
   
endmodule

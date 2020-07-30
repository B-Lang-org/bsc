
String readFile = "gettests.dat";

(* synthesize *)
module sysGetC_err1 () ;
     
   
   rule open ( True ) ;
      let lfh <- $fopen(readFile, "r" ) ;
      //  Need to use bind operation here.
      let i = $fgetc( lfh );
      int j = i + 5 ;
      $display( "reading the first character from %s is '%c' %h", readFile, j, j ) ;
      $fclose ( lfh ) ;
      $finish(0);
      
   endrule
   
   
endmodule

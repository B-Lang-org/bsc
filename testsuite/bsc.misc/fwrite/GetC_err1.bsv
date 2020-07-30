
String readFile = "gettests.dat";

(* synthesize *)
module sysGetC_err1 () ;
     
   
   rule open ( True ) ;
      let lfh <- $fopen(readFile, "r" ) ;
      //  Need to use bind operation here.
      int i = $fgetc( lfh );
      
      //$display( "reading the first character from %s is '%c' %h", readFile, i, i ) ;
      $fclose ( lfh ) ;
      $finish(0);
      
   endrule
   
   
endmodule

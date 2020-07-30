
String readFile = "xxx.dat";

(* synthesize *)
module sysFileTypeErr3 () ;
     
   
   rule open ( True ) ;
      //  Need to use bind operation here.
      File lfh = $fopen(readFile, "w" ) ;

      $fclose ( lfh ) ;
      $finish(0);
      
   endrule
   
   
endmodule

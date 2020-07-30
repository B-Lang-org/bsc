


(* synthesize *)
module sysGetC1 () ;
  
   rule open ( True ) ;
      String readFile = "gettests.dat";
      File lfh <- $fopen(readFile, "r" ) ;

      int i <- $fgetc( lfh );
      if ( i != -1 )
         begin
            Bit#(8) c = truncate( pack(i) ) ;  
         end
      else // an error occurred.
         begin
            $display( "Could not get byte from %s",
               readFile ) ;
         end
      
      $fclose ( lfh ) ;
      $finish(0);
      
   endrule
   
   
endmodule

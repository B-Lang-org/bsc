

String readFile = "gettests.dat";

(* synthesize *)
module sysGetC3 () ;
  
   rule open ( True ) ;
      let lfh <- $fopen(readFile, "r" ) ;
      
      $display( "=== Reading from %s ===", readFile ) ;
      Integer i ;
      
      int i0 ;
      for( i = 0 ; i < 100 ; i = i + 1)
         begin
            i0 <- $fgetc( lfh );
            if ( i0 != -1 )
               begin
                  Int#(8) c = truncate( i0 ) ;
                  $write( "%c", c );
                  if ( c == 101 )
                     begin
                        int x <- $ungetc( 33, lfh ) ;
                        if ( x == -1 ) $display ( "cannot unget " ) ;
                     end
               end
         end
      if ( i0 == -1 )
         begin
            $display( "=== Complete file read ===" ) ;
         end

      $fclose ( lfh ) ;
      $finish(0);
      
   endrule
   
   
endmodule


import FIFO :: * ;
import GetPut :: * ;


String readFile = "gettests.dat";

(* synthesize *)
module sysGetC2 () ;
  
   FIFO#(int) f <- mkFIFO;
   let fg = fifoToGet(f) ;
   
   rule open ( True ) ;
      let lfh <- $fopen(readFile, "r" ) ;
      int i <- $fgetc( lfh );
      let y = 5 ;
      let z = fg.get ;
      
      $display( "reading the first character from %s is '%c' %h", readFile, i, i, y ) ;
      $fclose ( lfh ) ;
      $finish(0);
      
   endrule
   
   
endmodule

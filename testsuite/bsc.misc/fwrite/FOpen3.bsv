
String dumpFile = "FOpen3.dat.out";

(* synthesize *)
module sysFOpen3 () ;
   
   rule open ( True ) ;
      // Unlike $time which we treat as a system Function, $fopen an
      // ActionValue function, and cannot be used in this way
      $fclose ( $fopen( dumpFile,"w") ) ;
      $finish(0);
   endrule
   
   
endmodule

// Test that the $signed functions are out of the generated code

(* synthesize *)
module sysSigned() ;
   
   // Use signed data
   Reg#(int) d <- mkReg(-4) ;
   
   rule check (True ) ;
      d <= d + 1 ;
      $display( "Showing signed data %0d", d );
      if ( d > 8 ) $finish(0) ;
   endrule
endmodule

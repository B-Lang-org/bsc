
module Param ( CLK,
               GO,
               RDY_GO
               ) ;

   // parameters are not in alphabetical or reverse order.
   parameter C = 0 ;
   parameter A = 0 ;
   parameter B = 0 ;

   input     CLK;
   input     GO;
   output    RDY_GO ;

   assign    RDY_GO = 1'b1 ;   

   always @ (posedge CLK )
     begin
        if ( GO )
           begin
              $display( "Parameter A is %d", A) ;
              $display( "Parameter B is %d", B) ;
              $display( "Parameter C is %d", C) ;
              $finish(0);
           end                 
     end // always @ (posedge CLK )

endmodule // Param

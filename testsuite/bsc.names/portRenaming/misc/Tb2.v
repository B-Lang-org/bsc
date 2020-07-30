// A test bench wrapper to check that port have been named correctly.

module Tb2 () ;

   wire x;
   assign x = 1'b1 ;
   
   mkSmallTest2 i1( .CLK(x),
                    .RST_N(x),

                    .TOPENQUEUE_data( { 32{x} } ),
                    .EN_topcenqueue({ x }),
                    .RDY_topcenqueue(),
                    
                    .XX_foo(),
                    .XX_xxx( 32'd1),
                    .XX_yyy( 32'd2),
                    
      
                    .YY_HEADelement(),
                    .YY_PrefixName__data_in({32{x}}),
                    .EN_YY_enqueue(x),
                    .YY_Data({32{x}}),
                    .YY_RDYenq2(),
                    .YY_ENQsafeToEnqueueOn2(x),
                    .YY_DEQRES(),
                    .EN_YY_dequeue(x),


                    
      
                    .AR_HEADelement(),
                    .AR_PrefixName__data_in({32{x}}),
                    .EN_AR_enqueue(x),
                    .AR_Data({32{x}}),
                    .AR_ENQsafeToEnqueueOn2(x),
                    .AR_DEQRES(),
                    .EN_AR_dequeue(x),


                    .AE_HEADelement(),
                    .AE_PrefixName__data_in({32{x}}),
                    .AE_Data({32{x}}),
                    .AE_DEQRES()

                    ) ;

   
   

endmodule

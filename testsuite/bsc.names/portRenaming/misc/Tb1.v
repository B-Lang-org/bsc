// A test bench wrapper to check that port have been named correctly.

module Tb1 () ;

   wire x;
   assign x = 1'b1 ;
   
   mkSmallTest1 i1( .CLK(x),
                    .RST_N(x),
                    .HEADelement(),
                    .PrefixName_data_in({3{x}}),
                    .EN1(x),
                    .Data({3{x}}),
                    .enq2RDYfoo(),
                    .ENQsafeToEnqueueOn2(x),
                    .DEQRES(),
                    .EN_dequeue(x)
                    ) ;

   
   

endmodule

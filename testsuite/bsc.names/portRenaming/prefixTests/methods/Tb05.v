// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_05  m1(.CLK(x),
		           .RST_N(x),
		           .variable__a({9{x}}),
		           .variable__b({9{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .variable__c({9{x}}),
		           .result(),
		           .RDY_result(x),
		   		   .variable__d({9{x}}),
		           .EN_check(x),
		           .check(),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

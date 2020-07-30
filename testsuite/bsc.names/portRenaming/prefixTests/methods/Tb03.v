// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_03  m1(.CLK(x),
		           .RST_N(x),
		           .Variable_a({7{x}}),
		           .Variable_b({7{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .Variable_c({7{x}}),
		           .result(),
		           .RDY_result(x),
		   		   .Variable_d({7{x}}),
		           .EN_check(x),
		           .check(),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_02  m1(.CLK(x),
		           .RST_N(x),
		           .variable_a({6{x}}),
		           .variable_b({6{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .variable_c({6{x}}),
		           .result(),
		           .RDY_result(x),
		   		   .variable_d({6{x}}),
		           .EN_check(x),
		           .check(),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

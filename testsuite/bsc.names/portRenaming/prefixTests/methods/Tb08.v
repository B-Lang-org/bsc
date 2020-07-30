// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_08  m1(.CLK(x),
		           .RST_N(x),
		           .variable_1_a({5{x}}),
		           .variable_1_b({5{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .variable_1_c({5{x}}),
		           .result(),
		           .RDY_result(x),
		   		   .variable_1_d({5{x}}),
		           .EN_check(x),
		           .check(),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

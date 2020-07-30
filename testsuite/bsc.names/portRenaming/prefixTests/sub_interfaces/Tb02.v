// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_02  m1(.CLK(x),
		           .RST_N(x),
		           .start_a({5{x}}),
		           .start_b({5{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .variable_result_c({5{x}}),
		           .variable_result(),
		           .RDY_variable_result(x),
		   		   .variable_check_d({5{x}}),
		           .EN_variable_check(x),
		           .variable_check(),
		           .RDY_variable_check(x)
                    ) ;

   
   

endmodule

// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_04  m1(.CLK(x),
		           .RST_N(x),
		           .start_a({7{x}}),
		           .start_b({7{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           ._variable_result_c({7{x}}),
		           ._variable_result(),
		           .RDY__variable_result(x),
		   		   ._variable_check_d({7{x}}),
		           .EN__variable_check(x),
		           ._variable_check(),
		           .RDY__variable_check(x)
                    ) ;

   
   

endmodule

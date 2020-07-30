// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_06  m1(.CLK(x),
		           .RST_N(x),
		           .start_a({8{x}}),
		           .start_b({8{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .var_name_result_c({8{x}}),
		           .var_name_result(),
		           .RDY_var_name_result(x),
		   		   .var_name_check_d({8{x}}),
		           .EN_var_name_check(x),
		           .var_name_check(),
		           .RDY_var_name_check(x)
                    ) ;

   
   

endmodule

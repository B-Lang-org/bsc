// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_06  m1(.CLK(x),
		           .RST_N(x),
		           .var_name_a({10{x}}),
		           .var_name_b({10{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .var_name_c({10{x}}),
		           .result(),
		           .RDY_result(x),
		   		   .var_name_d({10{x}}),
		           .EN_check(x),
		           .check(),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

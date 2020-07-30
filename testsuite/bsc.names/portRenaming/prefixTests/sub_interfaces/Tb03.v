// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_03  m1(.CLK(x),
		           .RST_N(x),
		           .start_a({6{x}}),
		           .start_b({6{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .Variable_result_c({6{x}}),
		           .Variable_result(),
		           .RDY_Variable_result(x),
		   		   .Variable_check_d({6{x}}),
		           .EN_Variable_check(x),
		           .Variable_check(),
		           .RDY_Variable_check(x)
                    ) ;

   
   

endmodule

// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_05  m1(.CLK(x),
		           .RST_N(x),
		           .start_a({6{x}}),
		           .start_b({6{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .variable__result_c({6{x}}),
		           .variable__result(),
		           .RDY_variable__result(x),
		   		   .variable__check_d({6{x}}),
		           .EN_variable__check(x),
		           .variable__check(),
		           .RDY_variable__check(x)
                    ) ;

   
   

endmodule

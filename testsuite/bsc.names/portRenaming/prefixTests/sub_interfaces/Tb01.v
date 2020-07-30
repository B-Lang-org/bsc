// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_01  m1(.CLK(x),
		           .RST_N(x),
		           .start_a({5{x}}),
		           .start_b({5{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .result_c({5{x}}),
		           .result(),
		           .RDY_result(x),
		   		   .check_d({5{x}}),
		           .EN_check(x),
		           .check(),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_04  m1(.CLK(x),
		           .RST_N(x),
		           ._variable_a({8{x}}),
		           ._variable_b({8{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           ._variable_c({8{x}}),
		           .result(),
		           .RDY_result(x),
		   		   ._variable_d({8{x}}),
		           .EN_check(x),
		           .check(),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

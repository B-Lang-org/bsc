// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_07  m1(.CLK(x),
		           .RST_N(x),
		           .var$name_a({11{x}}),
		           .var$name_b({11{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .var$name_c({11{x}}),
		           .result(),
		           .RDY_result(x),
		   		   .var$name_d({11{x}}),
		           .EN_check(x),
		           .check(),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

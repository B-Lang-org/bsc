// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_07  m1(.CLK(x),
		           .RST_N(x),
		           .start_a({5{x}}),
		           .start_b({5{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .var$name_result_c({5{x}}),
		           .var$name_result(),
		           .RDY_var$name_result(x),
		   		   .var$name_check_d({5{x}}),
		           .EN_var$name_check(x),
		           .var$name_check(),
		           .RDY_var$name_check(x)
                    ) ;

   
   

endmodule

// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   wire [4:0] result;
   wire [4:0] check;

   mkDesign_01  m1(.CLK(x),
		           .RST_N(x),
		           .a({5{x}}),
		           .b({5{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .c({5{x}}),
		           .result(result),
		           .RDY_result(x),
		   		   .d({5{x}}),
		           .EN_check(x),
		           .check(check),
		           .RDY_check(x)
                    ) ;

   
   

endmodule

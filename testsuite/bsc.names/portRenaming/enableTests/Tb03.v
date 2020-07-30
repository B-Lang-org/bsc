module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [6:0] result;
 wire [6:0] check;
 mkDesign_03 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 7{x}}),
		        .start_b({ 7{x}}),
		        .RDY_start(x),
		        ._stenable(y),
		        .result_c({ 7{x}}),
		        .result(result),
		        .RDY_result(y),
		        .check_d({ 7{x}}),
		        .RDY_check(x),
		        .check(check),
		        ._chenable(y)
				);
endmodule

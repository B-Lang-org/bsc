module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [4:0] result;
 wire [4:0] check;
 mkDesign_01 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 5{x}}),
		        .start_b({ 5{x}}),
		        .stenable(x),
				.RDY_start(y),
		        .result_c({ 5{x}}),
		        .result(result),
		        .RDY_result(y),
		        .check_d({ 5{x}}),
		        .check(check),
		        .chenable(x),
				.RDY_check(y)
				);
endmodule

module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [10:0] result;
 wire [10:0] check;
 
 mkDesign_07 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 11{x}}),
		        .start_b({ 11{x}}),
		        .RDY_start(x),
		        .stenable_1(y),
		        .result_c({ 11{x}}),
		        .result(result),
		        .RDY_result(y),
		        .check_d({ 11{x}}),
		        .RDY_check(x),
		        .check(check),
		        .chenable_1(y)
				);
endmodule

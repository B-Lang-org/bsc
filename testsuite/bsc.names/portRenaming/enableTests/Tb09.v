module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [4:0] result;
 wire [4:0] check;

 mkDesign_09 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 5{x}}),
		        .start_b({ 5{x}}),
		        .RDY_start(x),
		        .stenable(y),
		        .result_c({ 5{x}}),
		        .result(result),
		        .RDY_result(y),
		        .check_d({ 5{x}}),
		        .RDY_check(x),
		        .check(),
		        .chenable(y)
				);
endmodule

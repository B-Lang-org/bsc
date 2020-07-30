module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [5:0] result;
 wire [5:0] check;
 mkDesign_02 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 6{x}}),
		        .start_b({ 6{x}}),
		        .RDY_start(y),
		        .STenable(x),
		        .result_c({ 6{x}}),
		        .result(result),
				.RDY_result(y),
		        .check_d({ 6{x}}),
		        .RDY_check(x),
		        .check(check),
		        .CHenable(y)
				);
endmodule

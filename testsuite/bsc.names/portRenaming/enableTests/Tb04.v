module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [7:0] result;
 wire [7:0] check;
 mkDesign_04 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 8{x}}),
		        .start_b({ 8{x}}),
		        .RDY_start(x),
		        .stenable_(y),
		        .result_c({ 8{x}}),
		        .result(result),
		        .RDY_result(y),
		        .check_d({ 8{x}}),
		        .RDY_check(x),
		        .check(check),
		        .chenable_(y)
				);
endmodule

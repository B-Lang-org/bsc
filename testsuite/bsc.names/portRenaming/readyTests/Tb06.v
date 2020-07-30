module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [9:0] result;
 wire [9:0] check;
 mkDesign_06 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 10{x}}),
		        .start_b({ 10{x}}),
		        .EN_start(x),
		        .st$ready(y),
		        .result_c({ 10{x}}),
		        .result(result),
		        .res$ready(y),
		        .check_d({ 10{x}}),
		        .EN_check(x),
		        .check(check),
		        .ch$ready(y)
				);
endmodule

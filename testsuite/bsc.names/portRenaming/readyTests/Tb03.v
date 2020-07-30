module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [6:0] result;
 wire [6:0] check;
 mkDesign_03 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 7{x}}),
		        .start_b({ 7{x}}),
		        .EN_start(x),
		        ._stready(y),
		        .result_c({ 7{x}}),
		        .result(result),
		        ._resready(y),
		        .check_d({ 7{x}}),
		        .EN_check(x),
		        .check(check),
		        ._chready(y)
				);
endmodule

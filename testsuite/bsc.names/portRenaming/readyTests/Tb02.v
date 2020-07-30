module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [5:0] result;
 wire [5:0] check;
 
 mkDesign_02 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 6{x}}),
		        .start_b({ 6{x}}),
		        .EN_start(x),
		        .STready(y),
		        .result_c({ 6{x}}),
		        .result(result),
		        .RESready(y),
		        .check_d({ 6{x}}),
		        .EN_check(x),
		        .check(check),
		        .CHready(y)
				);
endmodule

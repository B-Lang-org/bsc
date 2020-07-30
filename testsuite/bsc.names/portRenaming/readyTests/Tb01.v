module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [4:0] result;
 wire [4:0] check;
 
 
 mkDesign_01 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 5{x}}),
		        .start_b({ 5{x}}),
		        .EN_start(x),
		        .stready(y),
		        .result_c({ 5{x}}),
		        .result(result),
		        .resready(y),
		        .check_d({ 5{x}}),
		        .EN_check(x),
		        .check(check),
		        .chready(y)
				);
endmodule

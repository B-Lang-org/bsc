module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [7:0] result;
 wire [7:0] check;

 mkDesign_04 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 8{x}}),
		        .start_b({ 8{x}}),
		        .EN_start(x),
		        .stready_(y),
		        .result_c({ 8{x}}),
		        .result(result),
		        .resready_(y),
		        .check_d({ 8{x}}),
		        .EN_check(x),
		        .check(check),
		        .chready_(y)
				);
endmodule

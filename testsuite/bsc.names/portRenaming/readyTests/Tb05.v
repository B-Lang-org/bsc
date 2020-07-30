module Tb ();

 wire x,y;
 assign x  = 1'b1;
 wire [8:0] result;
 wire [8:0] check;
 mkDesign_05 m1(.CLK(x),
		        .RST_N(x),
		        .start_a({ 9{x}}),
		        .start_b({ 9{x}}),
		        .EN_start(x),
		        .st_ready(y),
		        .result_c({ 9{x}}),
		        .result(result),
		        .res_ready(y),
		        .check_d({ 9{x}}),
		        .EN_check(x),
		        .check(check),
		        .ch_ready(y)
				);
endmodule

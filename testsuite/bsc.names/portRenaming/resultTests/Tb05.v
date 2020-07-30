module Tb();

 wire x,y;
 wire [9 - 1:0] result;
 wire [9 - 1:0] check;
 assign x = 1'b1;

 mkDesign_05 m1(.CLK(x),
		        .RST_N(x),
		        .start_a( {9{x}}),
		        .start_b( {9{x}}),
		        .EN_start(x),
		        .RDY_start(y),
		   	    .res_result(result),
		        .RDY_result(y),
		        .EN_check(x),
		        .ch_result(check),
		        .RDY_check(y)
				);

endmodule				

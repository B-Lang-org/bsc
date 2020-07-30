module Tb();

 wire x,y;
 wire [11 - 1:0] result;
 wire [11 - 1:0] check;
 assign x = 1'b1;

 mkDesign_07 m1(.CLK(x),
		        .RST_N(x),
		        .start_a( {11{x}}),
		        .start_b( {11{x}}),
		        .EN_start(x),
		        .RDY_start(y),
		   	    .resresult_1(result),
		        .RDY_result(y),
		        .EN_check(x),
		        .chresult_1(check),
		        .RDY_check(y)
				);

endmodule				

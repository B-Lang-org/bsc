module Tb();

 wire x,y;
 wire [8 - 1:0] result;
 wire [8 - 1:0] check;
 assign x = 1'b1;

 mkDesign_04 m1(.CLK(x),
		        .RST_N(x),
		        .start_a( {8{x}}),
		        .start_b( {8{x}}),
		        .EN_start(x),
		        .RDY_start(y),
		   	    .resresult_(result),
		        .RDY_result(y),
		        .EN_check(x),
		        .chresult_(check),
		        .RDY_check(y)
				);

endmodule				

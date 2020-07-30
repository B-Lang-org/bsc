module Tb();

 wire x,y;
 wire [10 - 1:0] result;
 wire [10 - 1:0] check;
 assign x = 1'b1;

 mkDesign_06 m1(.CLK(x),
		        .RST_N(x),
		        .start_a( {10{x}}),
		        .start_b( {10{x}}),
		        .EN_start(x),
		        .RDY_start(y),
		   	    .res$result(result),
		        .RDY_result(y),
		        .EN_check(x),
		        .ch$result(check),
		        .RDY_check(y)
				);

endmodule				

module Tb();

 wire x,y;
 wire [7 - 1:0] result;
 wire [7 - 1:0] check;
 assign x = 1'b1;

 mkDesign_03 m1(.CLK(x),
		        .RST_N(x),
		        .start_a( {7{x}}),
		        .start_b( {7{x}}),
		        .EN_start(x),
		        .RDY_start(y),
		   	    ._resresult(result),
		        .RDY_result(y),
		        .EN_check(x),
		        ._chresult(check),
		        .RDY_check(y)
				);

endmodule				

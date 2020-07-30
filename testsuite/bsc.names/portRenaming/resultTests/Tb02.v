module Tb();

 wire x,y;
 wire [6 - 1:0] result;
 wire [6 - 1:0] check;
 assign x = 1'b1;

 mkDesign_02 m1(.CLK(x),
		        .RST_N(x),
		        .start_a( {6{x}}),
		        .start_b( {6{x}}),
		        .EN_start(x),
		        .RDY_start(y),
		   	    .RESresult(result),
		        .RDY_result(y),
		        .EN_check(x),
		        .CHresult(check),
		        .RDY_check(y)
				);

endmodule				

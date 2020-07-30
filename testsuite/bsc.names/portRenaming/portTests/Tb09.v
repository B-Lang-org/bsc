module Tb();

wire x,y;
assign x = 1'b1;
wire [13 - 1:0] result;
wire [13 - 1:0] check;

mkDesign_09 m1(.CLK(x),
		       .RST_N(x),
		  	   .start_sta({ 13{x}}),
		       .start_stb({ 13{x}}),
		       .EN_start(x),
		       .RDY_start(y),
		   	   .result_stc({ 13{x}}),
		       .result(result),
		       .RDY_result(y),
		   	   .check_std({ 13{x}}),
		       .EN_check(x),
		       .check(check),
		       .RDY_check(y)
			   );
endmodule 


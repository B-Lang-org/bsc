module Tb();

wire x,y;
assign x = 1'b1;
wire [5 - 1:0] result;
wire [5 - 1:0] check;

mkDesign_01 m1(.CLK(x),
		       .RST_N(x),
		  	   .start_sta({ 5{x}}),
		       .start_stb({ 5{x}}),
		       .EN_start(x),
		       .RDY_start(y),
		   	   .result_stc({ 5{x}}),
		       .result(result),
		       .RDY_result(y),
		   	   .check_std({ 5{x}}),
		       .EN_check(x),
		       .check(check),
		       .RDY_check(y)
			   );
endmodule 


module Tb();

wire x,y;
assign x = 1'b1;
wire [7 - 1:0] result;
wire [7 - 1:0] check;

mkDesign_03 m1(.CLK(x),
		       .RST_N(x),
		  	   .start__sta({ 7{x}}),
		       .start__stb({ 7{x}}),
		       .EN_start(x),
		       .RDY_start(y),
		   	   .result__stc({ 7{x}}),
		       .result(result),
		       .RDY_result(y),
		   	   .check__std({ 7{x}}),
		       .EN_check(x),
		       .check(check),
		       .RDY_check(y)
			   );
endmodule 


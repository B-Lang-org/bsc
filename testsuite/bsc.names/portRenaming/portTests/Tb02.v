module Tb();

wire x,y;
assign x = 1'b1;
wire [6 - 1:0] result;
wire [6 - 1:0] check;

mkDesign_02 m1(.CLK(x),
		       .RST_N(x),
		  	   .start_Sta({ 6{x}}),
		       .start_Stb({ 6{x}}),
		       .EN_start(x),
		       .RDY_start(y),
		   	   .result_Stc({ 6{x}}),
		       .result(result),
		       .RDY_result(y),
		   	   .check_Std({ 6{x}}),
		       .EN_check(x),
		       .check(check),
		       .RDY_check(y)
			   );
endmodule 


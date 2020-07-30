module Tb();

wire x,y;
assign x = 1'b1;
wire [11 - 1:0] result;
wire [11 - 1:0] check;

mkDesign_07 m1(.CLK(x),
		       .RST_N(x),
		  	   .start_sta_1({ 11{x}}),
		       .start_stb_1({ 11{x}}),
		       .EN_start(x),
		       .RDY_start(y),
		   	   .result_stc_1({ 11{x}}),
		       .result(result),
		       .RDY_result(y),
		   	   .check_std_1({ 11{x}}),
		       .EN_check(x),
		       .check(check),
		       .RDY_check(y)
			   );
endmodule 


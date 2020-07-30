module Tb();

wire x,y;
assign x = 1'b1;
wire [8 - 1:0] result;
wire [8 - 1:0] check;

mkDesign_04 m1(.CLK(x),
		       .RST_N(x),
		  	   .start_sta_({ 8{x}}),
		       .start_stb_({ 8{x}}),
		       .EN_start(x),
		       .RDY_start(y),
		   	   .result_stc_({ 8{x}}),
		       .result(result),
		       .RDY_result(y),
		   	   .check_std_({ 8{x}}),
		       .EN_check(x),
		       .check(check),
		       .RDY_check(y)
			   );
endmodule 


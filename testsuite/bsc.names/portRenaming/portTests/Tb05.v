module Tb();

wire x,y;
assign x = 1'b1;
wire [9 - 1:0] result;
wire [9 - 1:0] check;

mkDesign_05 m1(.CLK(x),
		       .RST_N(x),
		  	   .start_st_a({ 9{x}}),
		       .start_st_b({ 9{x}}),
		       .EN_start(x),
		       .RDY_start(y),
		   	   .result_st_c({ 9{x}}),
		       .result(result),
		       .RDY_result(y),
		   	   .check_st_d({ 9{x}}),
		       .EN_check(x),
		       .check(check),
		       .RDY_check(y)
			   );
endmodule 


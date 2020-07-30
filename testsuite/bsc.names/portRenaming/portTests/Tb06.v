module Tb();

wire x,y;
assign x = 1'b1;
wire [10 - 1:0] result;
wire [10 - 1:0] check;

mkDesign_06 m1(.CLK(x),
		       .RST_N(x),
		  	   .start_st$a({ 10{x}}),
		       .start_st$b({ 10{x}}),
		       .EN_start(x),
		       .RDY_start(y),
		   	   .result_st$c({ 10{x}}),
		       .result(result),
		       .RDY_result(y),
		   	   .check_st$d({ 10{x}}),
		       .EN_check(x),
		       .check(check),
		       .RDY_check(y)
			   );
endmodule 


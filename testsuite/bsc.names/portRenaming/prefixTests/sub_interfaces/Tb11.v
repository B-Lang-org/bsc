module Tb();

wire x,y1,y2,y3,y4,y5,y6,y7,y8,y9;
assign x = 1'b1;

wire [5 - 1: 0] res0;
wire [5 - 1: 0] res1;
wire [5 - 1: 0] res2;

wire [5 - 1: 0] chk0;
wire [5 - 1: 0] chk1;
wire [5 - 1: 0] chk2;

mkDesign_11 m1 (.CLK(x),
		        .RST_N(x),
		        
				.XYZ_0_start_a({5 {x}}),
		        .XYZ_0_start_b({5 {x}}),
		        .EN_XYZ_0_start(x),
		        .RDY_XYZ_0_start(y1),
		   
		        .XYZ_0_result_c({5 {x}}),
		        .XYZ_0_result(res0),
		        .RDY_XYZ_0_result(y2),
		   
		        .XYZ_0_check_d({5 {x}}),
		        .EN_XYZ_0_check(x),
		        .XYZ_0_check(chk0),
		        .RDY_XYZ_0_check(y3),
		   
		        .XYZ_1_start_a({5 {x}}),
		        .XYZ_1_start_b({5 {x}}),
		        .EN_XYZ_1_start(x),
		        .RDY_XYZ_1_start(y4),
		   
		        .XYZ_1_result_c({5 {x}}),
		        .XYZ_1_result(res1),
		        .RDY_XYZ_1_result(y5),
		   
		        .XYZ_1_check_d({5 {x}}),
		        .EN_XYZ_1_check(x),
		        .XYZ_1_check(chk1),
		        .RDY_XYZ_1_check(y6),
		   
		        .XYZ_2_start_a({5 {x}}),
		        .XYZ_2_start_b({5 {x}}),
		        .EN_XYZ_2_start(x),
		        .RDY_XYZ_2_start(y7),
		   
		        .XYZ_2_result_c({5 {x}}),
		        .XYZ_2_result(res2),
		        .RDY_XYZ_2_result(y8),
		   
		        .XYZ_2_check_d({5 {x}}),
		        .EN_XYZ_2_check(x),
		        .XYZ_2_check(chk2),
		        .RDY_XYZ_2_check(y9)
				);

endmodule				

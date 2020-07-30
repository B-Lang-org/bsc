// A test bench wrapper to check that port have been named correctly.

module Tb () ;

   wire x;
   assign x = 1'b1 ;
   
   mkDesign_10  m1(.CLK(x),
		           .RST_N(x),
		           .start_a({5{x}}),
		           .start_b({5{x}}),
		           .EN_start(x),
		           .RDY_start(x),
		           .sub_ifc_$_result_c({5{x}}),
		           .sub_ifc_$_result(),
		           .RDY_sub_ifc_$_result(x),
		   		   .sub_ifc_$_check_d({5{x}}),
		           .EN_sub_ifc_$_check(x),
		           .sub_ifc_$_check(),
		           .RDY_sub_ifc_$_check(x)
                    ) ;

   
   

endmodule

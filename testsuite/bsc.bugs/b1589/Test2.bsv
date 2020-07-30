interface Ifc#(numeric type r, numeric type c);
endinterface

(* synthesize *)
module mkTest();
    Ifc#(3,3) m <- mkOne();
endmodule

module mkOne(Ifc#(3,3))
   provisos(Add#(0,3,c),
	    Add#(0,2,half_r), Add#(0,2,half_c),
	    Add#(0,1,other_half_r), Add#(0,1,other_half_c),

	    // these lead to trouble

	    Add#(half_r_minus_1,1,half_r),
	    Add#(c_minus_1, half_r, TSub#(TAdd#(half_r, c), 1)),
	    Add#(c_minus_1, other_half_r, TSub#(TAdd#(other_half_r, c), 1)),
	    Add#(TSub#(TAdd#(other_half_r, half_c), 1), other_half_c, TSub#(TAdd#(other_half_r, c), 1)),
	    Add#(TSub#(TAdd#(half_r, half_c), 1), other_half_c, TSub#(TAdd#(half_r, c), 1)),
	    Add#(TSub#(TAdd#(half_r, other_half_c), 1), half_c, TSub#(TAdd#(half_r, c), 1))

           );

   return ?;

endmodule

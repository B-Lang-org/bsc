interface Ifc#(numeric type r, numeric type c);
endinterface

(* synthesize *)
module mkTest();
    Ifc#(3,3) m <- mkOne();
endmodule

module mkOne(Ifc#(3,3))
   provisos(Add#(0,3,c),
	    Add#(0,2,half_r),
            Add#(0,2,unused), // This is not used anywhere, but does not fail without it!
	    Add#(0,1,other_half_r), Add#(0,1,other_half_c),

	    // these lead to trouble

	    /* c_minus_1 + 2 = 4 */
	    Add#(c_minus_1, 2, 4), // using Add#(c_minus_1, 0, 2) doesn't fail!
	    /* 2 + 1 = 1 + 3 - 1 */
	    Add#(c_minus_1, other_half_r, TSub#(TAdd#(other_half_r, c), 1)),
	    /* 1 + 2 - 1 + 1 = 1 + 3 - 1 */
	    Add#(TSub#(TAdd#(other_half_r, 2), 1), other_half_c, TSub#(TAdd#(other_half_r, c), 1)),
	    /* 2 + 1 - 1 + 2 = 2 + 3 - 1 */
	    Add#(TSub#(TAdd#(half_r, other_half_c), 1), 2, TSub#(TAdd#(half_r, 3), 1))

           );

   return ?;

endmodule

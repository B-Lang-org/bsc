interface Ouch#(numeric type lg_num_t);
endinterface

module mkOuch
	(Ouch#(lg_num_t))
	    provisos (Add#(TExp#(lg_num_t), 1, 2));
    return ?;
endmodule

(*synthesize*)
module test (Empty);
    Ouch#(0) ouch <- mkOuch;
endmodule


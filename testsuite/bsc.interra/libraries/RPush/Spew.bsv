package Spew;

import RPush :: *;

(* synthesize *)
module mkTestbench_Spew ();
    RPush #(Bit #(8)) src();
    sink the_src(src);
    Empty des();
    spew #(src) the_des(des);
    return des;
endmodule : mkTestbench_Spew


endpackage : Spew

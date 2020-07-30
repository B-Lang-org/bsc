package Spew;

import Push :: *;


module mkTestbench_Spew ();

   Push #(Bit #(8)) src();
   sink the_src(src);

   Empty des();
   spew #(src) the_des(des);
   
   rule done;
      let t <- $time();
      if (t > 1005)
         $finish(0);
   endrule
endmodule : mkTestbench_Spew


endpackage : Spew

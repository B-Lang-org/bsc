package Sink;

import Push :: *;

module mkTestbench_Sink ();
   Push #(Bit #(8)) dut();
   sink the_dut(dut);

   rule done;
      let t <- $time();
      if (t > 1005)
         $finish(0);
   endrule
   
endmodule : mkTestbench_Sink

endpackage : Sink
